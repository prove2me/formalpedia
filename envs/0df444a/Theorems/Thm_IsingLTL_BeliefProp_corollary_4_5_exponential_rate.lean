-- Prove2me | Theorems.Thm_IsingLTL_BeliefProp_corollary_4_5_exponential_rate
-- name    : IsingLTL.BeliefProp.corollary_4_5_exponential_rate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:20:21.11532+00:00
-- url     : https://prove2.me/theorems/3d2b7172-822d-43c8-889e-3af54d2e2967
-- title:
--   Theorem 4.2 with the exponential rate $\delta(t)=Ae^{-\lambda t}$ (Corollary 4.5, second clause)
-- statement:
--   Let $C=C(\beta_{\max},B_{\max})$ be the constant of Theorem 4.2. For $0<B_{\min}\le B_{\max}$ and $\beta_{\max}$, $\Delta$ finite there exist $A<\infty$ and $\lambda>0$, depending only on $\beta_{\max},B_{\min},B_{\max},\Delta$, such that the following holds. Let $\mathsf T$ be a conditionally independent tree with average offspring numbers bounded by $\Delta$, $0\le\beta\le\beta_{\max}$, $\ell>r$, and $\underline B$ a field with $B_i\le B_{\max}$ for all $i\in\mathsf T(\ell-1)$ and $B_i\ge B_{\min}$ for all $i\in\mathsf T(\ell)$. Then for every $U\subseteq\mathsf T(r)$,
--   $$\mathbb E\big\|\mu^{\ell,+}_U-\mu^{\ell,0}_U\big\|_{\mathrm{TV}}\le A\,e^{-\lambda(\ell-r)}\,\mathbb E\big\{C^{|\mathsf T(r)|}\big\}.$$
--
--   With this rate the effect of a plus boundary at distance $\ell-r$ decays exponentially, the form needed for Theorem 2.7.
--
--   **Formalization Note** Conventions for $U$, for the integrals in $[0,\infty]$ and for measurability are those of Theorem 4.2. The pair $(A,\lambda)$ of this statement may differ from the one of (4.13); the larger $A$ and the smaller $\lambda$ serve both.
-- source:
--   Dembo & Montanari, Ising Models on Locally Tree-Like Graphs, arXiv:0804.4726v3, p. 15, Corollary 4.5 (second clause), with Theorem 4.2, p. 11

import Mathlib
import Definitions.Def_IsingLTL_BeliefProp_CondIndepTree

namespace IsingLTL.BeliefProp

open MeasureTheory

/-- **Corollary 4.5, second clause** (Dembo–Montanari, arXiv:0804.4726v3, p. 15). There exist `A`
finite and `λ` positive, depending only on `β_max, B_min, B_max, Δ`, such that if `B_i ≤ B_max`
for all `i ∈ T(ℓ − 1)` then Theorem 4.2 holds for `δ(t) = A exp(−λt)`:
`E‖μ^{ℓ,+}_U − μ^{ℓ,0}_U‖_TV ≤ A e^{−λ(ℓ − r)} E{C^{|T(r)|}}` for all `U ⊆ T(r)`, `r < ℓ`.

Formalization Note: the hypotheses are those of Theorem 4.2 with `B_i ≤ B_max` required on
`T(ℓ − 1)` (words of length `+ 1 ≤ ℓ`) instead of `T(r − 1)`. `C = C(β_max, B_max)` is Theorem
4.2's constant, chosen as a function of `(β_max, B_max)` only; `A, λ` are chosen from
`β_max, B_min, B_max, Δ`, before the tree law, the field, `β`, `r`, `ℓ`. The pair `(A, λ)` of this
item need not equal the pair of (4.13); taking the larger `A` and smaller `λ` serves both. The
conventions for `U`, the integrals and measurability are those of Theorem 4.2. -/
theorem corollary_4_5_exponential_rate :
    ∃ C : ℝ → ℝ → ℝ, ∀ βmax Bmin Bmax Δ : ℝ, 0 < Bmin → Bmin ≤ Bmax →
      ∃ A lam : ℝ, 0 < lam ∧
        ∀ (μ : Measure (List ℕ → ℕ)) [IsProbabilityMeasure μ], IsingLTL.FreeEntropy.IsCondIndepTree μ Δ →
        ∀ (β : ℝ) (B : List ℕ → ℝ) (r ℓ : ℕ), 0 ≤ β → β ≤ βmax → r < ℓ →
          (∀ w : List ℕ, w.length + 1 ≤ ℓ → B w ≤ Bmax) →
          (∀ w : List ℕ, w.length ≤ ℓ → Bmin ≤ B w) →
          ∀ U : Finset (List ℕ) → Finset (List ℕ), (∀ s, U s ⊆ s) →
            Measurable (fun ω => tvDist
                (marginalOn (ballTree ω ℓ) (U (ballTree ω r)) (isingTree ω β B ℓ true))
                (marginalOn (ballTree ω ℓ) (U (ballTree ω r)) (isingTree ω β B ℓ false))) ∧
              ∫⁻ ω, ENNReal.ofReal (tvDist
                  (marginalOn (ballTree ω ℓ) (U (ballTree ω r)) (isingTree ω β B ℓ true))
                  (marginalOn (ballTree ω ℓ) (U (ballTree ω r)) (isingTree ω β B ℓ false))) ∂μ ≤
                ENNReal.ofReal (A * Real.exp (-lam * ((ℓ : ℝ) - r))) *
                  ∫⁻ ω, ENNReal.ofReal (C βmax Bmax ^ (ballTree ω r).card) ∂μ := by sorry

end IsingLTL.BeliefProp
