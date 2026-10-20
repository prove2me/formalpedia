-- Prove2me | Theorems.Thm_HealthRefPricing_PriceCompare_vp_price_unbounded
-- name    : HealthRefPricing.PriceCompare.vp_price_unbounded
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:23:38.411263+00:00
-- url     : https://prove2.me/theorems/b7290b52-075d-444a-84a0-0f733bbec27c
-- title:
--   Proof of Proposition 5, Appendix p. 9 (PDF 42) — as λ → 0 the VP equilibrium prices become arbitrarily large
-- statement:
--   Consider the two-provider model under the standing assumptions, with Assumption 1 holding at every cost share $\lambda \in (0,1]$. Then for each provider $j$ and every bound $M$ there is $\delta \in (0,1]$ such that for every cost share $\lambda \in (0,\delta)$ and every Nash equilibrium $P = (p_1,p_2)$ of the variable-payment price game at $\lambda$,
--
--   $$p_j > M .$$
--
--   In words, $p^{VP}_j \to \infty$ as $\lambda \to 0$: when patients pay almost nothing, the first-order condition can only be met at very high prices. Together with the comparison at $\lambda = 1$ this places the threshold $\lambda^*_j$ of Proposition 5 strictly inside $(0,1]$.
--
--   **Formalization Note** Provider $j$ ranges over `Fin 2`, index `0` being the paper's provider 1. The limit is written in $\varepsilon$–$\delta$ form over all equilibria at each small $\lambda$, so no equilibrium selection is assumed.
-- source:
--   Nassiri, Adida & Mamani, Reference pricing for healthcare services, author manuscript (SSRN 3176280, version of Dec. 28, 2020; eScholarship 3sm502rz), Appendix p. 9 (PDF 42), proof of Proposition 5, 'Moreover, as λ approaches zero, …'

import Mathlib
import Definitions.Def_HealthRefPricing_PriceCompare_Model

namespace HealthRefPricing.PriceCompare

/-- Proof of Proposition 5 (Appendix p. 9): as the cost share tends to zero, every
variable-payment equilibrium price becomes arbitrarily large. -/
theorem vp_price_unbounded (P : Params) (hS : P.Standing)
    (hA1 : ∀ lam ∈ Set.Ioc (0 : ℝ) 1, Assumption1 P lam) (j : Fin 2) (M : ℝ) :
    ∃ δ ∈ Set.Ioc (0 : ℝ) 1, ∀ lam ∈ Set.Ioo (0 : ℝ) δ, ∀ p : Fin 2 → ℝ, IsEqVP P lam p →
      M < p j := by sorry

end HealthRefPricing.PriceCompare
