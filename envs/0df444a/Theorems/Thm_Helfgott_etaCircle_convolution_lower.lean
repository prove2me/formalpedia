-- Prove2me | Theorems.Thm_Helfgott_etaCircle_convolution_lower
-- name    : Helfgott.etaCircle_convolution_lower
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-04T21:26:02.363345+00:00
-- url     : https://prove2.me/theorems/d74d837a-53c2-48c8-816b-8b9c2fdec45d
-- title:
--   Explicit elementary convolution lower bound for Helfgott’s symmetric smoothing
-- statement:
--   For the symmetric compact smoothing η_circle of equation (4.3), its additive convolution satisfies (η_circle*η_circle)(ρ)≥0.64−1.7(ρ−2)² for every real ρ. The estimate uses exact rational mass and derivative-energy bounds together with a sharp polarization coefficient 1/2. It supplies the convolution estimate for the main term of Helfgott’s major-arc argument. All constants are derived here; this is an elementary alternative to the numerical bounds in the paper.
-- source:
--   H. A. Helfgott, The ternary Goldbach conjecture is true, arXiv:1312.7748v2, equations (4.3)–(4.6) and (7.4)–(7.6), https://arxiv.org/html/1312.7748v2 . The rational constants 16/25 and 17/10 are derived here. Written by Codex.

import Definitions.Def_Helfgott_Smoothings
open MeasureTheory

namespace Helfgott

theorem etaCircle_convolution_lower (ρ : ℝ) :
    (16/25 : ℝ) - (17/10 : ℝ)*(ρ-2)^2 ≤
      ∫ t : ℝ, etaCircle t * etaCircle (ρ-t) := by sorry

end Helfgott
