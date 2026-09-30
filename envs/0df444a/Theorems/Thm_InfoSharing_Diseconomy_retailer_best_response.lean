-- Prove2me | Theorems.Thm_InfoSharing_Diseconomy_retailer_best_response
-- name    : InfoSharing.Diseconomy.retailer_best_response
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T05:58:05.224226+00:00
-- url     : https://prove2.me/theorems/f80b2ce1-61a4-40d5-ae15-195d7655d4e8
-- title:
--   §4.1, Eq. (1) — the retailer's best response and the resulting demand
-- statement:
--   Let $\phi > 0$ and $a, \beta \in \mathbb R$. A retail pricing rule $\rho(w, y)$ is a best response of the retailer, for all wholesale prices $w$ and all signal values $y$, if and only if
--
--   $$\hat p_i(w_i, w_j) = \tfrac12\big(a + \beta y + w_i\big), \qquad i = 1, 2.$$
--
--   Moreover, under this rule the realized demand at wholesale prices $w_i = f_i(Y)$ is
--
--   $$q_i = \tfrac12\big(a + \beta Y - (1+\phi)w_i + \phi w_j\big) + (\theta - \beta Y). \qquad (1)$$
--
--   This is the first step of the backward induction: it reduces the pricing game to a game between the manufacturers.
--
--   **Formalization Note.** The pricing stage is the Bayesian game of §4.1 on the signal model; the ex ante profits $M$, $R$ are those of an arbitrary pricing-equilibrium family, not the §4.2 closed forms. Wholesale strategies are measurable, square-integrable functions of the signal value (constants for an uninformed manufacturer); the production cost is $bq + cq^2$ with $c = c_d > 0$ and $b > 0$; manufacturers are indexed by $\{0,1\}$.
-- source:
--   Shang, Ha & Tong, Information Sharing in a Supply Chain with a Common Retailer, Management Sci. 62(1) 2016, p. 250, §4.1, Eq. (1)

import Mathlib
import Definitions.Def_InfoSharing_Shared_IsPricingEq
open InfoSharing.Shared

namespace InfoSharing.Diseconomy

/-- §4.1, Eq. (1), p. 250: the retailer's best-response retail price is
`p̂ᵢ(wᵢ, wⱼ) = ½(a + βY + wᵢ)`, and the resulting demand is
`qᵢ = ½(a + βY − (1+φ)wᵢ + φwⱼ) + (θ − βY)`. -/
theorem retailer_best_response {Ω : Type*} (a φ β : ℝ) (hφ : 0 < φ)
    (ρ : (Fin 2 → ℝ) → ℝ → (Fin 2 → ℝ)) :
    (IsRetailerBR a φ β ρ ↔ ∀ (w : Fin 2 → ℝ) (y : ℝ) (i : Fin 2), ρ w y i = (a + β * y + w i) / 2) ∧
    ∀ (θ Y : Ω → ℝ) (f : Fin 2 → ℝ → ℝ) (i : Fin 2) (ω : Ω), IsRetailerBR a φ β ρ →
      demand a φ θ Y ρ f i ω =
        (a + β * Y ω - (1 + φ) * f i (Y ω) + φ * f (other i) (Y ω)) / 2 + (θ ω - β * Y ω) := by sorry

end InfoSharing.Diseconomy
