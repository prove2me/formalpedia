-- Prove2me | Theorems.Thm_OfflineCensoredPricing_Identifiability_proposition_6
-- name    : OfflineCensoredPricing.Identifiability.proposition_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:32:41.723824+00:00
-- url     : https://prove2.me/theorems/01470a8b-0dc3-4774-8b09-afaa18bd79ed
-- title:
--   Proposition 6, p. 16 — if p*_max ≠ p*_min then Δ ≥ γb/(√γ + 1)² (p*_max − p*_min)²
-- statement:
--   Fix an instance satisfying the standing assumptions, with $\gamma = \mathbb P[\xi < \lambda] > 0$ and true price sensitivity $b$. Suppose $p^*_{\max} \ne p^*_{\min}$. Then the minimax revenue loss $\Delta = \min_{p\in[\underline p,\bar p]}\max_{F\in\mathcal F}\{R_F(p^*_F) - R_F(p)\}$ satisfies
--   $$\Delta \ge \frac{\gamma b}{(\sqrt\gamma + 1)^2}\,(p^*_{\max} - p^*_{\min})^2, \qquad (4)$$
--   equivalently, every price $p \in [\underline p,\bar p]$ has worst-case revenue loss at least $\frac{\gamma b}{(\sqrt\gamma+1)^2}(p^*_{\max} - p^*_{\min})^2$.
--
--   When the optimistic and pessimistic prices differ, no price, and hence no data-driven algorithm whatever its data, can guarantee a worst-case loss below this positive constant. This is the "only if" half of Theorem 1.
--
--   **Formalization Note** $\Delta$ is defined as the infimum of the worst-case loss over $[\underline p,\bar p]$; the second clause states the bound for each price directly, so it does not depend on the infimum being attained.
-- source:
--   Bu, Simchi-Levi & Wang, SSRN 3619625 (PDF of 2021-08-23), p. 16, Proposition 6, (4) (proof Appendix C.6, pp. 40–41)

import Mathlib
import Definitions.Def_OfflineCensoredPricing_Identifiability_Model

namespace OfflineCensoredPricing.Identifiability

open MeasureTheory Set

/-- **Proposition 6** (p. 16). Suppose `p*_max ≠ p*_min`. Then the minimax revenue loss is bounded
below as in (4): `Δ ≥ γb/(√γ + 1)² (p*_max − p*_min)²`; equivalently, every price `q ∈ [p̲, p̄]` has
worst-case revenue loss at least this constant. -/
theorem proposition_6 {K : ℕ} (I : Instance K) (hI : I.Standing) (hne : pStarMax I ≠ pStarMin I) :
    gam I * I.b / (Real.sqrt (gam I) + 1) ^ 2 * (pStarMax I - pStarMin I) ^ 2 ≤ Delta I ∧
      ∀ q ∈ Icc I.plo I.phi,
        gam I * I.b / (Real.sqrt (gam I) + 1) ^ 2 * (pStarMax I - pStarMin I) ^ 2 ≤
          worstLoss I q := by sorry

end OfflineCensoredPricing.Identifiability
