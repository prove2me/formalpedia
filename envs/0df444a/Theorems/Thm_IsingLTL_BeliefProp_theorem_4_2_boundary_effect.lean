-- Prove2me | Theorems.Thm_IsingLTL_BeliefProp_theorem_4_2_boundary_effect
-- name    : IsingLTL.BeliefProp.theorem_4_2_boundary_effect
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:19:27.814405+00:00
-- url     : https://prove2.me/theorems/6af5f78b-8dfc-461d-a00d-a22ea68bde60
-- title:
--   Plus and free boundary conditions give close marginals on $\mathsf T(r)$ (Theorem 4.2)
-- statement:
--   There exist finite constants $M=M(\beta_{\max},B_{\min},\Delta)$ and $C=C(\beta_{\max},B_{\max})$ such that the following holds whenever $0<B_{\min}\le B_{\max}$. Let $\mathsf T$ be a conditionally independent tree with average offspring numbers bounded by $\Delta$ (Definition 2.5), let $0\le\beta\le\beta_{\max}$ and $\ell>r$, and let $\underline B$ satisfy $B_i\le B_{\max}$ for all $i\in\mathsf T(r-1)$ and $B_i\ge B_{\min}$ for all $i\in\mathsf T(\ell)$. Then for every $U\subseteq\mathsf T(r)$,
--   $$\mathbb E\big\|\mu^{\ell,+}_U-\mu^{\ell,0}_U\big\|_{\mathrm{TV}}\le\delta(\ell-r)\,\mathbb E\big\{C^{|\mathsf T(r)|}\big\},\qquad\delta(t)=\frac Mt.$$
--
--   The theorem turns the root estimate of Lemma 4.3 into a bound on whole marginals near the root; Corollary 4.5 upgrades the rate $\delta$ to an exponential one.
--
--   **Formalization Note** $U$ may depend on the tree through $\mathsf T(r)$. Both expectations are integrals in $[0,\infty]$, since $\mathbb E\{C^{|\mathsf T(r)|}\}$ may be infinite. The conclusion also asserts that the total variation distance is a measurable function of the tree. The constants are chosen as functions of the indicated parameters only.
-- source:
--   Dembo & Montanari, Ising Models on Locally Tree-Like Graphs, arXiv:0804.4726v3, p. 11, Theorem 4.2, eq. (4.4)

import Mathlib
import Definitions.Def_IsingLTL_BeliefProp_CondIndepTree

namespace IsingLTL.BeliefProp

open MeasureTheory

/-- **Theorem 4.2** (Dembo–Montanari, arXiv:0804.4726v3, p. 11, eq. (4.4)). Suppose `T` is a
conditionally independent infinite tree of average offspring numbers bounded by `Δ`
(Definition 2.5). For `0 < B_min ≤ B_max`, `β_max` and `Δ` finite, there exist
`M = M(β_max, B_min, Δ)` and `C = C(β_max, B_max)` finite such that if `B_i ≤ B_max` for all
`i ∈ T(r − 1)` and `B_i ≥ B_min` for all `i ∈ T(ℓ)`, `ℓ > r`, then
`E‖μ^{ℓ,+}_U − μ^{ℓ,0}_U‖_TV ≤ δ(ℓ − r) E{C^{|T(r)|}}` with `δ(t) = M/t`, for all `U ⊆ T(r)` and
`β ≤ β_max`.

Formalization Note: the dependence of the constants is encoded by choosing them as functions,
`M β_max B_min Δ` and `C β_max B_max`, before everything else. `0 ≤ β` is the paper's standing
assumption. `U` may depend on the tree through `T(r)`: it is `U(T(r))` for a map `U` with
`U(s) ⊆ s`. `T(r − 1)` is the set of words of length `≤ r − 1` (empty when `r = 0`), written
`length + 1 ≤ r`. Both expectations are lower Lebesgue integrals in `ℝ≥0∞`, because
`E{C^{|T(r)|}}` may be `+∞`; the conclusion includes measurability of the total-variation
distance, so the left integral is its expectation. Bounds on the field over all words of a given
length are equivalent to bounds on `T(·)`, since values off the tree are not used. -/
theorem theorem_4_2_boundary_effect :
    ∃ M : ℝ → ℝ → ℝ → ℝ, ∃ C : ℝ → ℝ → ℝ, ∀ βmax Bmin Bmax Δ : ℝ, 0 < Bmin → Bmin ≤ Bmax →
      ∀ (μ : Measure (List ℕ → ℕ)) [IsProbabilityMeasure μ], IsingLTL.FreeEntropy.IsCondIndepTree μ Δ →
      ∀ (β : ℝ) (B : List ℕ → ℝ) (r ℓ : ℕ), 0 ≤ β → β ≤ βmax → r < ℓ →
        (∀ w : List ℕ, w.length + 1 ≤ r → B w ≤ Bmax) →
        (∀ w : List ℕ, w.length ≤ ℓ → Bmin ≤ B w) →
        ∀ U : Finset (List ℕ) → Finset (List ℕ), (∀ s, U s ⊆ s) →
          Measurable (fun ω => tvDist
              (marginalOn (ballTree ω ℓ) (U (ballTree ω r)) (isingTree ω β B ℓ true))
              (marginalOn (ballTree ω ℓ) (U (ballTree ω r)) (isingTree ω β B ℓ false))) ∧
            ∫⁻ ω, ENNReal.ofReal (tvDist
                (marginalOn (ballTree ω ℓ) (U (ballTree ω r)) (isingTree ω β B ℓ true))
                (marginalOn (ballTree ω ℓ) (U (ballTree ω r)) (isingTree ω β B ℓ false))) ∂μ ≤
              ENNReal.ofReal (M βmax Bmin Δ / ((ℓ : ℝ) - r)) *
                ∫⁻ ω, ENNReal.ofReal (C βmax Bmax ^ (ballTree ω r).card) ∂μ := by sorry

end IsingLTL.BeliefProp
