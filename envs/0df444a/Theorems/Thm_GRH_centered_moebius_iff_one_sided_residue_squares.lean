-- Prove2me | Theorems.Thm_GRH_centered_moebius_iff_one_sided_residue_squares
-- name    : GRH.centered_moebius_iff_one_sided_residue_squares
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T20:55:30.340483+00:00
-- url     : https://prove2.me/theorems/735514d1-0005-5a34-92cf-cf4af71a4b43
-- title:
--   Centered Möbius cancellation is equivalent to one-sided raw progression bounds at squares
-- statement:
--   The simultaneous centered bilinear power bound in every reduced residue class is equivalent to the following condition. For every modulus q, unit residue a, and exponent 1/2 < σ < 1, the raw sum of μ(n) over n ≤ u² in class a is bounded above by C(q,a,σ)(u²+1)^σ for all u.
-- source:
--   Arithmetic reduction of the exact centered progression estimate. https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006 The proved centered remainder and the principal residue estimate are used in the arithmetic transfer. https://prove2.me/theorems/99bde901-b30d-40ce-ae0f-029719b78029

import Definitions.Def_GRH_OneSidedMoebius

open MeasureTheory Set GRH.OneSidedMoebius

theorem GRH.centered_moebius_iff_one_sided_residue_squares : centeredBound ↔ squareUpper := by sorry
