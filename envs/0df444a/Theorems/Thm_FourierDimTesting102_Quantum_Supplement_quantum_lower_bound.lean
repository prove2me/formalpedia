-- Prove2me | Theorems.Thm_FourierDimTesting102_Quantum_Supplement_quantum_lower_bound
-- name    : FourierDimTesting102.Quantum.Supplement.quantum_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T03:27:52.190254+00:00
-- url     : https://prove2.me/theorems/0ba2fa6a-fbe7-4326-be02-3025d765d15f
-- title:
--   Theorem 3.2 — testing Fourier dimension $\le k$ needs $\Omega(k)$ quantum queries
-- statement:
--   Fix $0<\epsilon<1/4$. There are a constant $c>0$ and a threshold $K$, depending only on $\epsilon$, with the following property. Let $k\ge K$ and $n\ge k+1$, and let $A$ be any quantum query algorithm with oracle $O_f:|x\rangle|b\rangle\mapsto|x\rangle|b\oplus f(x)\rangle$ (arbitrary workspace, gates, intermediate measurements and classical randomness) that
--
--   1. accepts every boolean $f$ on $\mathbb F_2^n$ of Fourier dimension at most $k$ with probability at least $2/3$, and
--   2. rejects every $f$ with $\operatorname{dist}(f,D_k)\ge\epsilon$ with probability at least $2/3$.
--
--   Then on some input $f$, some run of $A$ of positive probability makes at least
--
--   $$
--   c\,k
--   $$
--
--   queries. So the $O(k/\sqrt\epsilon)$ tester of Theorem 3.1 is optimal in $k$ for each fixed $\epsilon$; the requirement $n\ge k+1$ is the nontrivial regime, since for $n\le k$ every boolean function has Fourier dimension at most $k$.
--
--   Differences from the source:
--   - encoding: boolean functions f : F₂ⁿ → {−1,1} → f is its bit function BoolFn n := (Fin n → ZMod 2) → Bool, with sign toSign f x = (−1)^{f x} (the base Model); reason: a bijection on the same functions; the bit is what the oracle returns
--   - reading: Fix ϵ < 1/4 → 0 < ε < 1/4; reason: ϵ-farness (Definition 2.5) is a positive parameter; for ε ≤ 0 every function of D_k is also ε-far and no algorithm distinguishes the two cases
--   - reading: requires at least Ω(k) quantum queries → ∃ c > 0, ∃ K, ∀ k ≥ K, ∀ n ≥ k + 1: some input has a positive-probability run with at least c·k queries; reason: Ω(k) is asymptotic in k with ϵ fixed, so c and K may depend on ϵ but not on n or A; the proof takes m = k + 1 and pads to n ≥ m variables, and for n ≤ k there are no no-instances
--   - encoding: a quantum tester with oracle O_f : |x⟩|b⟩ → |x⟩|b ⊕ f(x)⟩ (Definition 2.5) → an AdaptiveQueryAlg (V n) Bool: frozen query rounds with the published XOR oracle, arbitrary finite workspaces, full computational-basis measurements and classical branching; output true is accept; reason: covers unitary algorithms (one round), intermediate measurements and classical coins (zero-query rounds), as in the base mission
--   - encoding: distinguishes … with probability at least 2/3 → outProb f true ≥ 2/3 on every yes-instance and outProb f false ≥ 2/3 on every no-instance; reason: worst-case success over each promise side, as in Definition 2.5
--   - reading: ϵ-far from having Fourier dimension k → distToSet f (Dk n k) ≥ ε, with D_k the functions of Fourier dimension at most k; reason: p.13 and Definition 2.6 use “dimension k” for “at most k” and “far” for distance at least ϵ; the base goal reads it the same way
-- source:
--   Kenny Chen, Exponential Quantum Advantage in Testing Fourier Dimensionality, September 2026 STOC 2027 submission #102 preprint, source.pdf SHA-256 afe3d00f3d3887de87812ce319a69c1fca5c95912047974553110aa755de4298, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/102.pdf, p.16, Theorem 3.2 (proof pp.17–18, with Lemmas 3.4–3.5 and the cited Theorem 3.3 [KNP05])

import Definitions.Def_FourierDimTesting102_Quantum_Model
import Definitions.Def_QAlgorithms_Defs_AdaptiveQuery

namespace FourierDimTesting102.Quantum.Supplement

open QAlgorithms FourierDimTesting102.Quantum

/-- Theorem 3.2, p.16: fix `0 < ε < 1/4`. There are `c > 0` and `K` (depending on `ε` only) such
that for every `k ≥ K` and every `n ≥ k + 1`, every adaptive quantum query algorithm `A` (XOR
oracle, arbitrary finite workspaces, gates, intermediate measurements and classical coins) that
accepts (`true`) every `f` of Fourier dimension at most `k` with probability at least `2/3` and
rejects (`false`) every `f` with `dist(f, D_k) ≥ ε` with probability at least `2/3` makes at
least `c k` queries on some run of positive probability, on some input. -/
theorem quantum_lower_bound (ε : ℝ) (hε0 : 0 < ε) (hε : ε < 1 / 4) :
    ∃ c : ℝ, 0 < c ∧ ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ n : ℕ, k + 1 ≤ n →
      ∀ A : AdaptiveQueryAlg (V n) Bool,
        (∀ f : BoolFn n, fourierDim f ≤ k → 2 / 3 ≤ A.outProb f true) →
        (∀ f : BoolFn n, ε ≤ distToSet f (Dk n k) → 2 / 3 ≤ A.outProb f false) →
        ∃ f : BoolFn n, c * (k : ℝ) ≤ (A.maxQueries f : ℝ) := by sorry

end FourierDimTesting102.Quantum.Supplement
