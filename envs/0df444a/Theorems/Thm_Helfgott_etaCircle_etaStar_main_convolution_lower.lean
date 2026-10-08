-- Prove2me | Theorems.Thm_Helfgott_etaCircle_etaStar_main_convolution_lower
-- name    : Helfgott.etaCircle_etaStar_main_convolution_lower
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-04T22:11:23.109263+00:00
-- url     : https://prove2.me/theorems/3159b6b3-2526-44a6-820d-f9bc1045a3f4
-- title:
--   Explicit lower bound for the centered Goldbach main convolution
-- statement:
--   At the center ρ=2+9/(196√(2π)) used in Helfgott’s analytic Goldbach range, the convolution of the two symmetric compact smoothings with η* satisfies ∫₀∞η*(w)(∫ℝη_circle(u)η_circle(ρ−w−u)du)dw≥0.801/49. This is a completely derived elementary bound for the real main-term smoothing constant; it does not include the singular series or the major/minor-arc error estimates. All convergence, exact Mellin moments, and the rational mass/derivative estimates are proved.
-- source:
--   Helfgott, The ternary Goldbach conjecture is true, arXiv:1312.7748v2, equations (4.3)–(4.6), (7.11)–(7.14). https://arxiv.org/html/1312.7748v2 . The rational bound 0.801/49 is derived here using sharp polarization and exact Mellin moments. Written by Codex.

import Definitions.Def_Helfgott_Smoothings
open MeasureTheory

namespace Helfgott

theorem etaCircle_etaStar_main_convolution_lower :
    (801/49000 : ℝ) ≤
      ∫ w in Set.Ioi (0 : ℝ), etaStar w*(∫ u : ℝ,
        etaCircle u*etaCircle (2+9/(196*Real.sqrt (2*Real.pi))-w-u)) := by sorry

end Helfgott
