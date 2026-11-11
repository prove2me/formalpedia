-- Prove2me | Theorems.Thm_MatrixQuantumSampler595_Correspondence_extractor_sampler_correspondence
-- name    : MatrixQuantumSampler595.Correspondence.extractor_sampler_correspondence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:49:19.835664+00:00
-- url     : https://prove2.me/theorems/ca3e26cd-23bb-4065-bc0c-1cf8466a05ee
-- title:
--   Theorem 1.5 — quantum extractor–matrix sampler correspondence
-- statement:
--   Let $n,m$ be natural numbers, $t\ge1$, and let $F:\{0,1\}^n\times[t]\to\{0,1\}^m$ be an arbitrary map. Fix an integer $D\ge1$ and reals $0<\delta,\varepsilon<1$. All logarithms are base two. Then:
--
--   1. If $F$ is a strong (resp. weak) $\log(2D)$-qubit-proof $(n-\log(1/\delta),\ \varepsilon/2)$ extractor, then $F$ is a strong (resp. ordinary) $D$-dimensional $(\delta,\varepsilon)$ matrix sampler.
--   2. If $F$ is a strong (resp. ordinary) $D$-dimensional $(\delta,\varepsilon)$ matrix sampler, then for every real $a$ with $0\le a\le n$, $F$ is a strong (resp. weak) $(\log D)$-qubit-proof
--   $$\bigl(n-a,\ \tfrac{\varepsilon}{2}+2^{a}\delta\bigr)$$
--   extractor.
--
--   Here a $b$-qubit-proof extractor is secure against every cq source whose quantum register has dimension at most $2^b$ and whose classical part has min-entropy at least the stated threshold, with error measured in trace distance against $\tau_m\otimes\tau_{[t]}\otimes\rho_E$ (strong) or $\tau_m\otimes\rho_E$ (weak); matrix samplers bound the probability, over a uniform $x\in\{0,1\}^n$, that the empirical average of the tests deviates from their mean by more than $\varepsilon$ in operator norm.
--
--   The theorem is a quantum, matrix-valued analogue of Zuckerman's correspondence between averaging samplers and extractors: quantum side information of dimension about $D$ corresponds to $D\times D$ matrix-valued tests, and a public seed corresponds to position-dependent tests. It is used to turn quantum-proof extractor constructions into explicit matrix samplers.
--
--   Differences from the source:
--   - encoding: $F:\{0,1\}^n\times[t]\to\{0,1\}^m$ with uniform seed on $[t]$ → `F : BitString n → Fin t → BitString m` with the explicit hypothesis `0 < t`; reason: $[t]$ is indexed by `Fin t`, and the source's uniform seed and factor $1/t$ presuppose $t\ge1$.
--   - encoding: "$b$-qubit-proof", $\dim E\le 2^b$ with $b=\log(2D)$ or $\log D$ → register $\mathbb C^q$ for every natural $q$ with $q\le 2^b$ (real power, `Real.logb 2`); reason: $2^{\log_2(2D)}=2D$ and $2^{\log_2 D}=D$ exactly, every finite-dimensional register is isomorphic to some $\mathbb C^q$, and no rounding to integral qubits is introduced.
--   - encoding: four implications with "resp." → one conjunction of four implications; reason: the conjunction states each of the source's strong and weak/ordinary cases separately.
--   - encoding: uniform probabilities and expectations on bit strings, with the Euclidean operator norm → finite cardinality divided by $2^n$, finite sums divided by $2^m$, and Mathlib's scoped `Matrix.Norms.L2Operator`; reason: `BitString n` has exactly $2^n$ elements and the scoped norm is the norm of `Matrix.toEuclideanCLM`, so these are the same probability, mean and norm.
--   - encoding: normalized cq states, classical min-entropy, and actual/ideal quantum outputs → PSD blocks with real traces summing to one, the point-mass inequalities $\operatorname{Re}\operatorname{Tr}\sigma_x\le2^{-k}$, and full block-diagonal output matrices; reason: PSD traces are real, the finite normalized marginal has positive maximum mass, and its min-entropy bound is equivalent to these inequalities; the constructed matrices are exactly the source's actual states and products with its actual marginal, with trace distance $\tfrac12\operatorname{Tr}\sqrt{A^*A}$.
-- source:
--   Kuan Cheng, Ruiyang Wu, Matrix Samplers and Quantum-Proof Extractors: Their Correspondence and Almost-Optimal Constructions, STOC 2027 submission #595 (October 2026), Theorem 1.5, p.5; restated p.14, proof pp.14–16

import Mathlib
import Definitions.Def_MatrixQuantumSampler595_Correspondence_MatrixSampler
import Definitions.Def_MatrixQuantumSampler595_Correspondence_QuantumProofExtractor

namespace MatrixQuantumSampler595.Correspondence

/-- Theorem 1.5 (p.5, restated p.14): quantum extractor–matrix sampler correspondence. -/
theorem extractor_sampler_correspondence {n m t : ℕ} (ht : 0 < t)
    (F : BitString n → Fin t → BitString m) (D : ℕ) (hD : 1 ≤ D) (δ ε : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hε0 : 0 < ε) (hε1 : ε < 1) :
    (IsStrongQubitProofExtractor F (Real.logb 2 (2 * D)) (n - Real.logb 2 (1 / δ)) (ε / 2) →
      IsStrongMatrixSampler F D δ ε) ∧
    (IsWeakQubitProofExtractor F (Real.logb 2 (2 * D)) (n - Real.logb 2 (1 / δ)) (ε / 2) →
      IsMatrixSampler F D δ ε) ∧
    (IsStrongMatrixSampler F D δ ε → ∀ a : ℝ, 0 ≤ a → a ≤ n →
      IsStrongQubitProofExtractor F (Real.logb 2 D) (n - a) (ε / 2 + (2 : ℝ) ^ a * δ)) ∧
    (IsMatrixSampler F D δ ε → ∀ a : ℝ, 0 ≤ a → a ≤ n →
      IsWeakQubitProofExtractor F (Real.logb 2 D) (n - a) (ε / 2 + (2 : ℝ) ^ a * δ)) := by sorry

end MatrixQuantumSampler595.Correspondence
