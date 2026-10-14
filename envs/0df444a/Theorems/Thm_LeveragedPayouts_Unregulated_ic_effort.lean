-- Prove2me | Theorems.Thm_LeveragedPayouts_Unregulated_ic_effort
-- name    : LeveragedPayouts.Unregulated.ic_effort
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:25:06.759829+00:00
-- url     : https://prove2.me/theorems/0442b5b6-1993-4f5c-8dc5-5f43d94e9b99
-- title:
--   Appendix B, proof of Proposition 2, p. 52 — the incentive constraint (6) holds exactly when e = πx
-- statement:
--   Let $\pi>0$ and let $x,e$ be real numbers. The effort $e$ maximizes the shareholder's net utility $y\mapsto xy-y^2/(2\pi)$ if and only if
--   $$e=\pi x.$$
--
--   This is the first step of the proof of Proposition 2: it turns the incentive constraint (6)/(32) into an explicit formula, so that the firm's program reduces to a choice of the retained stake $x$ and of investment.
-- source:
--   Acharya & Plantin, Monetary Easing, Leveraged Payouts, and Lack of Investment, SSRN 3484935 (version of May 23, 2023), p. 52, Appendix B, proof of Proposition 2

import Mathlib
import Definitions.Def_LeveragedPayouts_Unregulated_Firm

namespace LeveragedPayouts.Unregulated
theorem ic_effort (π : ℝ) (hπ : 0 < π) (x e : ℝ) : IsIC π x e ↔ e = π * x := by sorry
end LeveragedPayouts.Unregulated
