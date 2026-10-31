-- Prove2me | Theorems.Thm_OfflineCensoredPricing_Identifiability_proposition_7
-- name    : OfflineCensoredPricing.Identifiability.proposition_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:32:44.738283+00:00
-- url     : https://prove2.me/theorems/2303b9e3-feea-46ac-bd72-275e4e2fa0f7
-- title:
--   Proposition 7, p. 20 — the worst-case revenue loss of any price equals max{Rmax(p*_max) − Rmax(p), Rmin(p*_min) − Rmin(p)}
-- statement:
--   Fix an instance satisfying the standing assumptions. For any price $p \in [\underline p,\bar p]$, the worst-case revenue loss over the ambiguity set is attained and satisfies
--   $$\max_{F\in\mathcal F}\{R_F(p^*_F) - R_F(p)\} = \max\{R_{\max}(p^*_{\max}) - R_{\max}(p),\ R_{\min}(p^*_{\min}) - R_{\min}(p)\}. \qquad (5)$$
--
--   Only the best-possible and the worst-possible distributions matter for the worst-case loss. This identity turns the minimax revenue loss into a problem about two explicit curves, and D2ACD prices by minimizing its empirical counterpart.
--
--   **Formalization Note** $R_F(p^*_F)$ is written $\sup_{q\in[\underline p,\bar p]} R_F(q)$, its value. The statement asserts that the right-hand side is the greatest element of $\{R_F(p^*_F) - R_F(p) : F\in\mathcal F\}$ and equals the worst-case loss as defined (a supremum).
-- source:
--   Bu, Simchi-Levi & Wang, SSRN 3619625 (PDF of 2021-08-23), p. 20, Proposition 7, (5) (proof Appendix D.3, pp. 48–51)

import Mathlib
import Definitions.Def_OfflineCensoredPricing_Identifiability_Model

namespace OfflineCensoredPricing.Identifiability

open MeasureTheory Set

/-- **Proposition 7** (p. 20). For any price `q ∈ [p̲, p̄]`, the worst-case revenue loss satisfies (5):
`max_{F ∈ 𝓕} {R_F(p*_F) − R_F(q)} = max{R_max(p*_max) − R_max(q), R_min(p*_min) − R_min(q)}`,
the maximum over the ambiguity set being attained. -/
theorem proposition_7 {K : ℕ} (I : Instance K) (hI : I.Standing) (q : ℝ)
    (hq : q ∈ Icc I.plo I.phi) :
    IsGreatest ((fun μ => sSup (RF I μ '' Icc I.plo I.phi) - RF I μ q) '' Amb I)
        (max (Rmax I (pStarMax I) - Rmax I q) (Rmin I (pStarMin I) - Rmin I q)) ∧
      worstLoss I q =
        max (Rmax I (pStarMax I) - Rmax I q) (Rmin I (pStarMin I) - Rmin I q) := by sorry

end OfflineCensoredPricing.Identifiability
