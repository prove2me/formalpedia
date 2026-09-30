-- Prove2me | Theorems.Thm_InfoSharing_Economy_lemma_1_pricing_equilibrium
-- name    : InfoSharing.Economy.lemma_1_pricing_equilibrium
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T23:42:45.082615+00:00
-- url     : https://prove2.me/theorems/1f26794d-fc10-4edb-a1e8-dd9e171f6a48
-- title:
--   Lemma 1 — the unique pricing equilibrium is linear in the demand signal (production economy)
-- statement:
--   Let $\phi > 0$ and $0 < c_e < 2/(1+\phi)$, put $c = -c_e$, and let $a, b$ be reals. Let $(\theta, Y)$ satisfy the signal model with variance $\sigma^2$ and weight $\beta = \beta(t,\sigma)$. For every status profile $X$ the pricing game of §4.1 has an equilibrium, and, provided $c_e \ne c_e^*$ (see the note), in every equilibrium $(\rho, f)$, for each manufacturer $i$, almost surely
--
--   $$w_i^* = f_i(Y) = \bar w + \alpha_w\,Y, \qquad p_i^* = \rho(w^*, Y)_i = \bar p + \alpha_p\,Y,$$
--
--   where $\bar w = \frac{(1+(1+\phi)c)a + (1+\phi)b}{2+\phi+(1+\phi)c}$, $\bar p = \frac{(3+\phi+2(1+\phi)c)a + (1+\phi)b}{2(2+\phi+(1+\phi)c)}$, and $\alpha_w$, $\alpha_p$ are the coefficients of Lemma 1 selected by $n$ and, when $n = 1$, by $X_i$:
--
--   1. $\alpha_w(0) = \alpha_w^U(1) = 0$, $\alpha_w^I(1) = \frac{1+(1+\phi)c}{(1+\phi)(2+(1+\phi)c)}\beta$, $\alpha_w(2) = \frac{1+(1+\phi)c}{2+\phi+(1+\phi)c}\beta$;
--   2. $\alpha_p(0) = \alpha_p^U(1) = \frac{\beta}{2}$, $\alpha_p^I(1) = \frac{3+2\phi+(1+\phi)(2+\phi)c}{2(1+\phi)(2+(1+\phi)c)}\beta$, $\alpha_p(2) = \frac{3+\phi+2(1+\phi)c}{2(2+\phi+(1+\phi)c)}\beta$.
--
--   An informed manufacturer's wholesale price responds to the signal, positively when $c_e < 1/(1+\phi)$ and negatively when $c_e > 1/(1+\phi)$; an uninformed one's does not. All ex ante profits of §4.2 follow from this equilibrium.
--
--   **Formalization Note** The production economy model takes $c = -c_e$ with $0 < c_e < 2/(1+\phi)$ (the Assumption of p. 251). The ex ante profits are those of an equilibrium of the pricing game on the signal model, not the closed forms: the closed forms are the content of the §4.2 milestones. The production cost is the uncapped quadratic $bq - c_e q^2$ (the paper's cap at $\bar q = b/(2c_e)$ is assumed never to bind, footnote 11, p. 251). **Correction of the paper.** Uniqueness is asserted only for $c_e \ne$ $c_e^* = \frac{2+3\phi}{(1+2\phi)(1+\phi)}$. At $c_e^*$ the slope $\phi(1+(1+\phi)c)/[(1+\phi)(2+(1+\phi)c)]$ of the best response (2) equals $-1$, the linear system $w_i = \hat w_i(w_j)$ is singular, and every profile has a continuum of equilibria (for instance $w_{1,2} = \bar w \pm t$ when $n = 0$) with different profits; the proof of Lemma 1 (p. 260) overlooks this. Existence holds for every $c_e$.
-- source:
--   Shang, Ha & Tong, Information Sharing in a Supply Chain with a Common Retailer, Management Sci. 62(1) 2016, p. 251, Lemma 1 (with $\bar w$, $\bar p$ from the paragraph above it)

import Mathlib
import Definitions.Def_InfoSharing_Shared_IsSignalModel
import Definitions.Def_InfoSharing_Shared_PayoffTable
import Definitions.Def_InfoSharing_Shared_ClosedForms
open MeasureTheory
open InfoSharing.Shared

namespace InfoSharing.Economy

/-- **Lemma 1** (Shang, Ha & Tong 2016, p. 251), production economy (`c = −c_e`) under the
Assumption `c_e < 2/(1+φ)` (p. 251). For every information-status profile `X` the pricing stage
has an equilibrium, and (for `c_e ≠ (2+3φ)/((1+2φ)(1+φ))`, see below) in every equilibrium
manufacturer `i`'s wholesale price is
`w̄ + α_w · Y` and the retail price of product `i` is `p̄ + α_p · Y` (a.s.), with the
coefficients of the lemma (`alphaW`, `alphaP`, which depend on `n` and on `X i`).

**Correction.** Uniqueness is asserted for `c_e ≠ (2+3φ)/((1+2φ)(1+φ))`. At that value the
slope `φ(1+(1+φ)c)/((1+φ)(2+(1+φ)c))` of the best response (2) equals `−1`, the linear system
`w_i = ŵ_i(w_j)` is singular, and every profile has a continuum of equilibria; the paper's
uniqueness claim (proof of Lemma 1, p. 260) fails there. Existence holds for all `c_e`. -/
theorem lemma_1_pricing_equilibrium (φ ce c a b σ β : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (θ Y : Ω → ℝ) (hφ : 0 < φ) (hc : c = -ce) (hce : 0 < ce)
    (hA : ce < 2 / (1 + φ)) (hM : IsSignalModel μ θ Y σ β) (X : Fin 2 → Status) :
    (∃ (ρ : (Fin 2 → ℝ) → ℝ → (Fin 2 → ℝ)) (f : Fin 2 → ℝ → ℝ),
      IsPricingEq μ θ Y a b c φ β X ρ f) ∧
    (ce ≠ (2 + 3 * φ) / ((1 + 2 * φ) * (1 + φ)) → ∀ (ρ : (Fin 2 → ℝ) → ℝ → (Fin 2 → ℝ)) (f : Fin 2 → ℝ → ℝ),
      IsPricingEq μ θ Y a b c φ β X ρ f → ∀ i : Fin 2,
        (∀ᵐ ω ∂μ, f i (Y ω) = wbar a b c φ + alphaW c φ β X i * Y ω) ∧
        (∀ᵐ ω ∂μ, ρ (fun j => f j (Y ω)) (Y ω) i = pbar a b c φ + alphaP c φ β X i * Y ω)) := by sorry

end InfoSharing.Economy
