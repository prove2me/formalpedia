-- Prove2me | Theorems.Thm_InfoSharing_Diseconomy_lemma_1_pricing_equilibrium
-- name    : InfoSharing.Diseconomy.lemma_1_pricing_equilibrium
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T06:02:12.142775+00:00
-- url     : https://prove2.me/theorems/1ed52f75-3532-4ca2-be78-dbd4a989e1b7
-- title:
--   Lemma 1 — the unique pricing equilibrium is linear in the demand signal
-- statement:
--   Let $(\theta, Y)$ be a signal model with parameters $\sigma, \beta$, and let $\phi > 0$, $b > 0$, $c = c_d > 0$. For every status profile $X$ with $n$ informed manufacturers, the pricing game has an equilibrium, and in every equilibrium the retailer uses $\hat p_i = \frac12(a + \beta y + w_i)$ and, almost surely,
--
--   $$w_i^* = \bar w + \alpha_w Y, \qquad p_i^* = \bar p + \alpha_p Y,$$
--
--   where $\alpha_w, \alpha_p$ are $\alpha_w(n), \alpha_p(n)$ if $n \in \{0, 2\}$ and $\alpha_w^{X_i}(1), \alpha_p^{X_i}(1)$ if $n = 1$, with the values of Lemma 1 (see the closed-forms definition).
--
--   Lemma 1 is what makes the ex ante profits computable: every equilibrium is linear in the signal.
--
--   **Formalization Note.** The pricing stage is the Bayesian game of §4.1 on the signal model; the ex ante profits $M$, $R$ are those of an arbitrary pricing-equilibrium family, not the §4.2 closed forms. Wholesale strategies are measurable, square-integrable functions of the signal value (constants for an uninformed manufacturer); the production cost is $bq + cq^2$ with $c = c_d > 0$ and $b > 0$; manufacturers are indexed by $\{0,1\}$. Uniqueness of the wholesale strategies is almost sure, since they are determined only on the law of $Y$.
-- source:
--   Shang, Ha & Tong, Information Sharing in a Supply Chain with a Common Retailer, Management Sci. 62(1) 2016, p. 251, Lemma 1

import Mathlib
import Definitions.Def_InfoSharing_Shared_IsSignalModel
import Definitions.Def_InfoSharing_Shared_IsPricingEq
import Definitions.Def_InfoSharing_Shared_ClosedForms
open MeasureTheory
open InfoSharing.Shared

namespace InfoSharing.Diseconomy

/-- Lemma 1, p. 251 (production diseconomy, `c = c_d > 0`): for every status profile `X` the
pricing game has an equilibrium, and in every equilibrium the retailer uses
`p̂ᵢ = ½(a + βy + wᵢ)` and, `μ`-a.e., `wᵢ* = w̄ + α_w Y` and `pᵢ* = p̄ + α_p Y` with the
coefficients of Lemma 1 for manufacturer `i`'s status and the number of informed
manufacturers. -/
theorem lemma_1_pricing_equilibrium {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (θ Y : Ω → ℝ) (a b c φ σ β : ℝ) (hmodel : IsSignalModel μ θ Y σ β) (hφ : 0 < φ)
    (hb : 0 < b) (hc : 0 < c) (X : Fin 2 → Status) :
    (∃ (ρ : (Fin 2 → ℝ) → ℝ → (Fin 2 → ℝ)) (f : Fin 2 → ℝ → ℝ),
        IsPricingEq μ θ Y a b c φ β X ρ f) ∧
    ∀ (ρ : (Fin 2 → ℝ) → ℝ → (Fin 2 → ℝ)) (f : Fin 2 → ℝ → ℝ),
      IsPricingEq μ θ Y a b c φ β X ρ f →
        (∀ (w : Fin 2 → ℝ) (y : ℝ) (i : Fin 2), ρ w y i = (a + β * y + w i) / 2) ∧
        ∀ i : Fin 2,
          (fun ω => f i (Y ω)) =ᵐ[μ] (fun ω => wbar a b c φ + alphaW c φ β X i * Y ω) ∧
          (fun ω => ρ (fun j => f j (Y ω)) (Y ω) i) =ᵐ[μ]
            (fun ω => pbar a b c φ + alphaP c φ β X i * Y ω) := by sorry

end InfoSharing.Diseconomy
