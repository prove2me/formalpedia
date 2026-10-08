-- Prove2me | Theorems.Thm_Helfgott_reference_etaCircle_etaStar_main_convolution_lower_tight
-- name    : Helfgott.reference_etaCircle_etaStar_main_convolution_lower_tight
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-06T04:44:14.558708+00:00
-- url     : https://prove2.me/theorems/08a9d28e-06da-4c5f-b3a1-cbd590184164
-- title:
--   Sharp centered reference convolution for the three-prime Goldbach major term
-- statement:
--   For Helfgott's compact symmetric reference smoothing $\eta_\circ$, the actual star smoothing $\eta_*$, and $\rho=2+9/(196\sqrt{2\pi})$, the reference convolution satisfies
--   $$\int_0^\infty\eta_*(w)\int_{\mathbb R}\eta_\circ(u)\eta_\circ(\rho-w-u)\,du\,dw\ge\frac{0.8022}{49}.$$
--   This improves the previous unconditional $0.801/49$ reference lower bound. It retains the negative centering term in the exact star variance and uses complete rational polynomial bounds for the reference mass and derivative energy. The approximation from $\eta_\circ$ to the actual band-limited smoothing $\eta_+$ remains a separate obligation toward the mission's actual major-arc lower bound.
-- source:
--   Helfgott, The ternary Goldbach conjecture is true, https://arxiv.org/html/1312.7748v2, section 7.2. Original rational Taylor and centered variance refinement. Written by Codex.

import Definitions.Def_Helfgott_Smoothings
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Pow.Real
open MeasureTheory

namespace Helfgott

theorem reference_etaCircle_etaStar_main_convolution_lower_tight :
    (4011/5000 : ℝ)/49≤
      ∫ w in Set.Ioi (0 : ℝ),etaStar w*(∫ u : ℝ,
        etaCircle u*etaCircle (2+9/(196*Real.sqrt (2*Real.pi))-w-u)) := by sorry

end Helfgott
