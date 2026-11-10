-- Prove2me | Theorems.Thm_OnlineDiscUniv_theorem_1_3
-- name    : OnlineDiscUniv.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:15:28.406517+00:00
-- url     : https://prove2.me/theorems/cb52eb4e-ed25-4bff-8b55-d0fad5c3b2b3
-- title:
--   Theorem 1.3 (Quantitative upper bound) — $\mathbb P_\mu(D_{M,N}>\kappa)+\mathbb E_\mu(D_{M,N}-\kappa)_+\le C_A[N^{-A}+t_\mu(N^{1/3})]$
-- statement:
--   Fix $\alpha>0$, $\kappa>R_\alpha$, $K<\infty$ and $A>0$. There is a randomized online algorithm, depending only on these parameters, such that every centered law $\mu$ with variance one and $\mathbb E_\mu|\xi|^4\le K$ satisfies
--   $$
--   \mathbb P_\mu(D_{M,N}>\kappa)+\mathbb E_\mu(D_{M,N}-\kappa)_+\le C_A\big[N^{-A}+t_\mu(N^{1/3})\big].\qquad(1.1)
--   $$
--   The bound holds uniformly for all sufficiently large $N$ and all $M/N$ in a sufficiently small fixed neighborhood of $\alpha$. The constant, the neighborhood and the lower bound on $N$ depend only on $(\alpha,\kappa,K,A)$.
--
--   This is the achievability half of Theorem 1.1, with a rate.
--
--   Differences from the source:
--   - generalization: a fixed standard Brownian motion B with its completed natural filtration → every process B with IsBrownianReal B P on every probability space, the values computed on that B; reason: the Brownian control values depend only on the law of B; the source's Brownian motion is one such process
--   - encoding: ε_k = A_{k,M,N}(U, ξ_1, …, ξ_k) ∈ {−1,+1} → sign maps jointly measurable in (seed, input), constant in columns after k; reason: measurability is implicit in the paper (probabilities and expectations of D_{M,N} must be defined); causality is the online constraint
--   - reading: a randomized online algorithm, depending only on (α, κ, K, A) → a family alg M N (one for every pair (M, N)) with seed unitInterval under Lebesgue measure, chosen before µ and M (after the Brownian triple, which enters only through the number R_α); reason: a specific seed space is stronger than an unspecified one; the conclusion does not involve B and R_α depends only on the law of B
--   - encoding: the exponent A; probabilities, expectations and t_µ → the exponent is named Aexp; values in ℝ≥0∞, C embedded by ENNReal.ofReal; reason: name clash with the algorithm; same inequality
-- source:
--   Jo, Lee, Exact Universality of Online Discrepancy, arXiv:2610.00103 (artifact sha256 cb190f127dea2c038b4a22a4787862f82356a983593dfdc3dc3fe3c7c8264ad5), Theorem 1.3, (1.1), p.2 (PDF p.3)

import Mathlib
import Definitions.Def_OnlineDiscUniv_Ralpha
import Definitions.Def_OnlineDiscUniv_MomentClass
import Definitions.Def_OnlineDiscUniv_optDisc

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace OnlineDiscUniv

/-- **Theorem 1.3 (Quantitative upper bound)** (Jo–Lee, arXiv:2610.00103, artifact sha256
cb190f12…, printed p.2, PDF p.3). Fix `α > 0`, `κ > R_α`, `K < ∞`, and `A > 0`. There is a
randomized online algorithm, depending only on these parameters, such that every centered law `μ`
with variance one and `E_μ|ξ|⁴ ≤ K` satisfies
`P_μ(D_{M,N} > κ) + E_μ(D_{M,N} − κ)_+ ≤ C_A [N^{−A} + t_μ(N^{1/3})]` (1.1). The bound holds
uniformly for all sufficiently large `N` and all `M/N` in a sufficiently small fixed neighborhood
of `α`. The constant, the neighborhood, and the lower bound on `N` depend only on `(α, κ, K, A)`.

**Formalization Note** The exponent `A` is named `Aexp` (the algorithm is `alg`). The algorithm is
a family `alg M N`, one for every pair `(M, N)`, with seed `unitInterval` under Lebesgue measure
(a particular seed space, which is stronger than "some seed"). `alg`, `C`, the neighborhood
radius `η` and `N₀` are chosen before `μ` and `M`; the Brownian motion `B` only serves to define
the number `R_α`, which depends on its law alone. Probabilities, expectations and `t_μ` are in
`ℝ≥0∞`. -/
theorem theorem_1_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (α : ℝ) (hα : 0 < α) (κ : ℝ)
    (hκ : Ralpha P B α < ENNReal.ofReal κ) (K Aexp : ℝ) (hA : 0 < Aexp) :
    ∃ alg : (M N : ℕ) → OnlineAlg unitInterval M N, ∃ C η : ℝ, ∃ N₀ : ℕ, 0 < η ∧
      ∀ N M : ℕ, N₀ ≤ N → |(M : ℝ) / N - α| < η → ∀ μ ∈ MomentClass 4 K,
        failProb μ (volume : Measure unitInterval) (alg M N) κ +
            expExcess μ (volume : Measure unitInterval) (alg M N) κ ≤
          ENNReal.ofReal C * (ENNReal.ofReal ((N : ℝ) ^ (-Aexp)) +
            tailMod μ ((N : ℝ) ^ ((1 : ℝ) / 3))) := by sorry

end OnlineDiscUniv
