-- Prove2me | Theorems.Thm_MazurHuang_N19_raw_chart_normalized_polynomial_identity
-- name    : MazurHuang.N19.raw_chart_normalized_polynomial_identity
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-07T18:12:41.803896+00:00
-- url     : https://prove2.me/theorems/972be982-2b31-4310-bc7d-8cacc83d129c
-- title:
--   The normalized raw-chart polynomial residual
-- statement:
--   The denominator-cleared raw-chart residual after removing (s−1)² equals −(s²−r−s+1)² times the fourth power of the horizontal numerator factor and the raw polynomial. Shifted coordinates expose the F⁴ factor before the final lower-degree polynomial calculation.
-- source:
--   Apache-2.0; fork 51bbb4f191ad0d3753b87123635c100a638ae580; FLT/Assumptions/MazurProof/N19SutherlandModels.lean:24-40; FLT/Assumptions/MazurProof/N19SutherlandModels.lean:63-80; FLT/Assumptions/MazurProof/N19SutherlandModels.lean:179-196

import Mathlib

theorem MazurHuang.N19.raw_chart_normalized_polynomial_identity (r s : ℚ) : (fun (T F N A D : ℚ) =>
      T^3*N^5*D^2 - T^2*(T^2*F^2+2*D^2)*N^4*A*D
      + T*(2*T^3*F^3-2*T^2*F^2*D+2*T*F*D^2+D^3)*N^3*A^2*D
      + (-T^5*F^5+3*T^4*F^4*D-7*T^3*F^3*D^2+6*T^2*F^2*D^3-2*T*F*D^4)*N^2*A^3
      + (T^4*F^5-2*T^3*F^4*D+4*T^2*F^3*D^2-3*T*F^2*D^3)*N*A^4*D
      - T*F^3*A^5*D^4 + F^2*A^5*D^5) (s-1) ((fun (r s : ℚ) => r * s - 2 * r + 1) r s) ((fun (r s : ℚ) => r ^ 2 * s - 3 * r ^ 2 + r * s + 3 * r - s ^ 2 - 1) r s) (r-s) ((fun (r s : ℚ) => r * s ^ 2 - 3 * r * s + r + s ^ 2) r s) = -(s^2-r-s+1)^2 * (fun (r s : ℚ) => r * s - 2 * r + 1) r s^4 * (fun (r s : ℚ) => r ^ 6
      - r ^ 5 * s ^ 7 + 11 * r ^ 5 * s ^ 6 - 48 * r ^ 5 * s ^ 5
      + 105 * r ^ 5 * s ^ 4 - 121 * r ^ 5 * s ^ 3
      + 69 * r ^ 5 * s ^ 2 - 20 * r ^ 5 * s - r ^ 5
      - 2 * r ^ 4 * s ^ 7 + 12 * r ^ 4 * s ^ 6 - 9 * r ^ 4 * s ^ 5
      - 60 * r ^ 4 * s ^ 4 + 144 * r ^ 4 * s ^ 3
      - 105 * r ^ 4 * s ^ 2 + 35 * r ^ 4 * s
      - 3 * r ^ 3 * s ^ 7 + 3 * r ^ 3 * s ^ 6 + 21 * r ^ 3 * s ^ 5
      - 30 * r ^ 3 * s ^ 4 - 41 * r ^ 3 * s ^ 3
      + 51 * r ^ 3 * s ^ 2 - 21 * r ^ 3 * s
      + r ^ 2 * s ^ 9 - 6 * r ^ 2 * s ^ 8 + 21 * r ^ 2 * s ^ 7
      - 50 * r ^ 2 * s ^ 6 + 66 * r ^ 2 * s ^ 5
      - 31 * r ^ 2 * s ^ 4 + 25 * r ^ 2 * s ^ 3
      - 18 * r ^ 2 * s ^ 2 + 7 * r ^ 2 * s
      + 3 * r * s ^ 6 - 15 * r * s ^ 5 + 10 * r * s ^ 4
      - 6 * r * s ^ 3 + 3 * r * s ^ 2 - r * s + s ^ 6) r s := by sorry
