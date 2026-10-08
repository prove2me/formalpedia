-- Prove2me | Theorems.Thm_Helfgott_actual_etaPlus_etaStar_main_convolution_lower_tight_complete
-- name    : Helfgott.actual_etaPlus_etaStar_main_convolution_lower_tight_complete
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-06T05:36:42.622474+00:00
-- url     : https://prove2.me/theorems/4640de0e-6c38-44d2-a122-9a86ef6caa34
-- title:
--   Sharp complete actual smoothing convolution for the original three-prime major arcs
-- statement:
--   Let $\eta_+$ and $\eta_*$ be the actual smoothings in the three-prime Goldbach proof and put $\rho=2+9/(196\sqrt{2\pi})$. The complete main convolution is integrable and satisfies
--   $$\int_0^\infty\eta_*(w)\int_{\mathbb R}\eta_+(u)\eta_+(\rho-w-u)\,du\,dw\ge\frac{0.80214}{49}.$$
--   This includes the full error of the actual band-limited smoothing. Combined with the odd singular constant and the sharp finite-model and prime-error estimates, it supplies the original major-arc lower coefficient. No numerical zero-location or prime-accuracy hypothesis is required.
-- source:
--   Helfgott, The ternary Goldbach conjecture is true, https://arxiv.org/html/1312.7748v2, section 7.2. Complete rational Fourier-kernel and smoothing-error refinement. Written by Codex.

import Definitions.Def_Helfgott_Smoothings
import Mathlib.MeasureTheory.Integral.Bochner.Set
open MeasureTheory Set

namespace Helfgott

theorem actual_etaPlus_etaStar_main_convolution_lower_tight_complete :
    IntegrableOn (fun w : ℝ => etaStar w*(∫ u : ℝ,
      etaPlus u*etaPlus (2+9/(196*Real.sqrt (2*Real.pi))-w-u))) (Ioi (0 : ℝ)) ∧
    (40107/50000 : ℝ)/49 ≤
      ∫ w in Ioi (0 : ℝ), etaStar w*(∫ u : ℝ,
        etaPlus u*etaPlus (2+9/(196*Real.sqrt (2*Real.pi))-w-u)) := by sorry

end Helfgott
