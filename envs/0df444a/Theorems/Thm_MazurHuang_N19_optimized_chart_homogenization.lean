-- Prove2me | Theorems.Thm_MazurHuang_N19_optimized_chart_homogenization
-- name    : MazurHuang.N19.optimized_chart_homogenization
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-07T18:12:22.080231+00:00
-- url     : https://prove2.me/theorems/6c8ebb68-46cb-4cb7-aa10-2e17cf48b1b2
-- title:
--   Weighted homogenization of the optimized plane equation
-- statement:
--   For a chart with x=−TF/D and y=TN/(AD), the optimized order-nineteen plane polynomial equals T² times its displayed homogeneous residual divided by A⁵D⁷.
-- source:
--   Apache-2.0; fork 51bbb4f191ad0d3753b87123635c100a638ae580; FLT/Assumptions/MazurProof/N19SutherlandModels.lean:52-59; FLT/Assumptions/MazurProof/N19SutherlandModels.lean:179-196

import Mathlib

theorem MazurHuang.N19.optimized_chart_homogenization (T F N A D : ℚ) (hA : A ≠ 0) (hD : D ≠ 0) : (fun (x y : ℚ) => y ^ 5
      - (x ^ 2 + 2) * y ^ 4
      - (2 * x ^ 3 + 2 * x ^ 2 + 2 * x - 1) * y ^ 3
      + (x ^ 5 + 3 * x ^ 4 + 7 * x ^ 3 + 6 * x ^ 2 + 2 * x) * y ^ 2
      - (x ^ 5 + 2 * x ^ 4 + 4 * x ^ 3 + 3 * x ^ 2) * y
      + x ^ 3 + x ^ 2) (-T*F/D) (T*N/(A*D)) = T^2 * (fun (T F N A D : ℚ) =>
      T^3*N^5*D^2 - T^2*(T^2*F^2+2*D^2)*N^4*A*D
      + T*(2*T^3*F^3-2*T^2*F^2*D+2*T*F*D^2+D^3)*N^3*A^2*D
      + (-T^5*F^5+3*T^4*F^4*D-7*T^3*F^3*D^2+6*T^2*F^2*D^3-2*T*F*D^4)*N^2*A^3
      + (T^4*F^5-2*T^3*F^4*D+4*T^2*F^3*D^2-3*T*F^2*D^3)*N*A^4*D
      - T*F^3*A^5*D^4 + F^2*A^5*D^5) T F N A D / (A^5*D^7) := by sorry
