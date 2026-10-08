-- Prove2me | Theorems.Thm_IsingLTL_FreeEntropy_theorem_2_4_free_entropy
-- name    : IsingLTL.FreeEntropy.theorem_2_4_free_entropy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:13:30.266248+00:00
-- url     : https://prove2.me/theorems/93800bee-9852-485d-9fc1-4d02ddd698ca
-- title:
--   Theorem 2.4 — the Ising free entropy density on locally tree-like graphs converges to the Bethe prediction (2.9)
-- statement:
--   Let $\{G_n\}_{n\in\mathbb N}$ be a sequence of uniformly sparse graphs, $G_n$ on $[n]$, that converges locally to $T(P,\rho,\infty)$, where $\rho$ has finite first moment (equivalently, $P$ has finite second moment). Then for every $B\in\mathbb R$ and $\beta\ge0$ the limit
--   $$\lim_{n\to\infty}\frac1n\log Z_n(\beta,B)=\phi(\beta,B)$$
--   exists. For $B>0$ it is given by
--   $$\phi(\beta,B)=\frac{\bar P}{2}\log\cosh(\beta)-\frac{\bar P}{2}\,\mathbb E\log[1+\tanh(\beta)\tanh(h_1)\tanh(h_2)]+\mathbb E\log\Big\{e^B\prod_{i=1}^L[1+\tanh(\beta)\tanh(h_i)]+e^{-B}\prod_{i=1}^L[1-\tanh(\beta)\tanh(h_i)]\Big\},$$
--   where $L\sim P$ is independent of the cavity fields $h_i$, i.i.d. copies of the fixed point $h^*$ of Lemma 2.3. Moreover $\phi(\beta,B)=\phi(\beta,-B)$, and $\phi(\beta,0)$ is the limit of $\phi(\beta,B)$ as $B\to0$.
--
--   Concretely, writing $\phi^+(\beta,B)$ for the right-hand side of (2.9) at $B>0$:
--
--   1. for $B>0$, $\frac1n\log Z_n(\beta,B)\to\phi^+(\beta,B)$;
--   2. for $B<0$, $\frac1n\log Z_n(\beta,B)\to\phi^+(\beta,-B)$;
--   3. $\phi^+(\beta,B)$ has a limit $L_0$ as $B\downarrow0$, and $\frac1n\log Z_n(\beta,0)\to L_0$.
--
--   This confirms the cavity-method prediction for the free entropy per spin at every temperature and field.
--
--   **Formalization Note** $h^*$ is the fixed point of (2.6) at $(\beta,B)$ supported on $[0,\infty)$, which exists and is unique under these hypotheses by Lemma 2.3. Every edge is counted once in $Z_n$.
-- source:
--   Dembo & Montanari, Ising Models on Locally Tree-Like Graphs, arXiv:0804.4726v3, pp. 5-6, Theorem 2.4, (2.8)-(2.9)

import Mathlib
import Definitions.Def_IsingLTL_FreeEntropy_PartitionFunction
import Definitions.Def_IsingLTL_FreeEntropy_LocalConvergence
import Definitions.Def_IsingLTL_FreeEntropy_BetheFunctional

namespace IsingLTL.FreeEntropy

open MeasureTheory Filter Topology

/-- **Theorem 2.4** (Dembo–Montanari, *Ising Models on Locally Tree-Like Graphs*,
arXiv:0804.4726v3, pp. 5–6, eqs. (2.8)–(2.9)). Let `{G_n}` be a sequence of uniformly sparse graphs
that converges locally to `T(P, ρ, ∞)`. If `ρ` has finite first moment (that is, if `P` has finite
second moment), then for any `B ∈ ℝ` and `β ≥ 0` the limit
`lim_{n→∞} (1/n) log Z_n(β, B) = φ(β, B)` (2.8) exists. Moreover, for `B > 0` the limit is
`φ(β, B) = (P̄/2) log cosh β − (P̄/2) E log[1 + tanh β tanh h₁ tanh h₂]
  + E log{e^B ∏_{i=1}^L [1 + tanh β tanh h_i] + e^{−B} ∏_{i=1}^L [1 − tanh β tanh h_i]}` (2.9),
where `L ∼ P` is independent of the cavity fields `h_i`, i.i.d. copies of the fixed point `h*` of
Lemma 2.3. Also `φ(β, B) = φ(β, −B)`, and `φ(β, 0)` is the limit of `φ(β, B)` as `B → 0`.

Formalization Note. The conclusion has three parts, which together say that the limit exists for
every `B ∈ ℝ` and identify it:
1. for `B > 0`, `φ_n(β, B) → φ⁺(β, B)`, where `φ⁺(β, B)` is (2.9) evaluated at the law of `h*`, the
   fixed point of (2.6) at `(β, B)` supported on `[0, ∞)` (`betheFreeEntropy`; Lemma 2.3 says it
   exists and is unique);
2. for `B < 0`, `φ_n(β, B) → φ⁺(β, −B)` (this is `φ(β, B) = φ(β, −B)`);
3. `φ⁺(β, B)` has a limit `L₀` as `B → 0⁺`, and `φ_n(β, 0) → L₀` (this is "`φ(β, 0)` is the limit of
   `φ(β, B)` as `B → 0`"; by 2 the two-sided limit is the same).
`G_n` is a graph on `Fin n` (`V_n = [n]`); `φ_n = (1/n) log Z_n` with every edge counted once in
(1.1). "`ρ` has finite first moment" is `∑ k ρ_k < ∞`. -/
theorem theorem_2_4_free_entropy (G : ∀ n : ℕ, SimpleGraph (Fin n)) [∀ n, DecidableRel (G n).Adj]
    (D : DegreeDist) (hsparse : UniformlySparse G) (hloc : ConvergesLocally G D)
    (hρ : D.RhoFiniteMean) (β : ℝ) (hβ : 0 ≤ β) :
    (∀ B : ℝ, 0 < B →
        Tendsto (fun n : ℕ => freeEntropyDensity (G n) β B) atTop
          (𝓝 (betheFreeEntropy β B D))) ∧
      (∀ B : ℝ, B < 0 →
        Tendsto (fun n : ℕ => freeEntropyDensity (G n) β B) atTop
          (𝓝 (betheFreeEntropy β (-B) D))) ∧
      ∃ L₀ : ℝ, Tendsto (fun B : ℝ => betheFreeEntropy β B D) (𝓝[>] 0) (𝓝 L₀) ∧
        Tendsto (fun n : ℕ => freeEntropyDensity (G n) β 0) atTop (𝓝 L₀) := by sorry

end IsingLTL.FreeEntropy
