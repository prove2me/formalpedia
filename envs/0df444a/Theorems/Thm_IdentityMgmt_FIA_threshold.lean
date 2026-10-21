-- Prove2me | Theorems.Thm_IdentityMgmt_FIA_threshold
-- name    : IdentityMgmt.FIA.threshold
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:19:57.026894+00:00
-- url     : https://prove2.me/theorems/e23563e5-2064-4fb5-8c54-3dd538395874
-- title:
--   Proof of Proposition 1, OA p. 5 (PDF 59) — in an FIA MPE, θ̃ < 1 and θ_inf > 0 iff c < c̄^FIA
-- statement:
--   In every quasi-linear FIA Markov perfect equilibrium, with discount factor $\beta$, privacy cost $c$, cut-off slope $\gamma$ and threshold
--   $$\bar c^{FIA} = \frac{\beta(1-\gamma)(1+(1-2\beta)\gamma)}{(1-\beta\gamma)^2},$$
--   one has
--   $$\big(\tilde\theta < 1 \text{ and } \theta_{\inf} > 0\big) \iff c < \bar c^{FIA}.$$
--
--   That is, active customers exist and some low types are never served exactly when the privacy cost is below the threshold.
-- source:
--   Laussel, Long & Resende, Profit Effects of Consumers' Identity Management: A Dynamic Model, CIRANO working paper 2021s-29 (24 Aug. 2021), Online Appendix, OA p. 5 (PDF 59), proof of Proposition 1 ("One checks that θ̃^FIA < 1 and θ_inf > 0 iff c < c̄^FIA")

import Mathlib
import Definitions.Def_IdentityMgmt_FIA_Model

namespace IdentityMgmt.FIA

theorem threshold (P : Profile) (hP : P.IsMPE) :
    (P.θt < 1 ∧ 0 < P.θinf) ↔ P.c < cbarFIA P.β P.γ := by sorry

end IdentityMgmt.FIA
