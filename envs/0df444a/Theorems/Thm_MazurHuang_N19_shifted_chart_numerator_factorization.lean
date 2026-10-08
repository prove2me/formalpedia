-- Prove2me | Theorems.Thm_MazurHuang_N19_shifted_chart_numerator_factorization
-- name    : MazurHuang.N19.shifted_chart_numerator_factorization
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-07T18:13:02.406212+00:00
-- url     : https://prove2.me/theorems/cb521475-ca1b-46af-9e36-6fcb509c970c
-- title:
--   Factorization of the shifted-chart homogeneous numerator
-- statement:
--   In shifted coordinates, substituting N=(A+T)F−A² and D=(T+1)F−TA into the homogeneous residual yields the displayed polynomial in F, with a common F² factor and additional factors AT−A+T² in its low coefficients.
-- source:
--   Apache-2.0; fork 51bbb4f191ad0d3753b87123635c100a638ae580; FLT/Assumptions/MazurProof/N19SutherlandModels.lean:63-80; FLT/Assumptions/MazurProof/N19SutherlandModels.lean:179-196

import Mathlib
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem MazurHuang.N19.shifted_chart_numerator_factorization (A T F : ℚ) :
  let chartHomogeneous : ℚ → ℚ → ℚ → ℚ → ℚ → ℚ := (fun (T F N A D : ℚ) =>
      T^3*N^5*D^2 - T^2*(T^2*F^2+2*D^2)*N^4*A*D
      + T*(2*T^3*F^3-2*T^2*F^2*D+2*T*F*D^2+D^3)*N^3*A^2*D
      + (-T^5*F^5+3*T^4*F^4*D-7*T^3*F^3*D^2+6*T^2*F^2*D^3-2*T*F*D^4)*N^2*A^3
      + (T^4*F^5-2*T^3*F^4*D+4*T^2*F^3*D^2-3*T*F^2*D^3)*N*A^4*D
      - T*F^3*A^5*D^4 + F^2*A^5*D^5)
  let chartC7 : ℚ → ℚ → ℚ := fun (A T : ℚ) => A^5+A^4*T^5+A^4*T^4-2*A^4*T^3-4*A^4*T^2+A^3*T^6+3*A^3*T^5+4*A^3*T^4+A^3*T^3+A^2*T^8-4*A^2*T^6-2*A^2*T^5+A^2*T^4+2*A*T^9+3*A*T^8-A*T^7-2*A*T^6+T^10+2*T^9+T^8
  let chartC6 : ℚ → ℚ → ℚ := fun (A T : ℚ) => -A*T*(A^5*T^3+A^5*T^2-2*A^5*T+A^5+A^4*T^5+4*A^4*T^4-8*A^4*T^2+2*A^4*T+4*A^3*T^6+6*A^3*T^5-2*A^3*T^3+3*A^3*T^2+8*A^2*T^7+4*A^2*T^6-10*A^2*T^5-4*A^2*T^4+8*A*T^8+8*A*T^7-A*T^6+2*T^9+2*T^8)
  let chartK5 : ℚ → ℚ → ℚ := fun (A T : ℚ) => A^4*T^3+4*A^4*T^2+A^4*T-A^4+5*A^3*T^4+7*A^3*T^3-6*A^3*T^2-3*A^3*T+10*A^2*T^5+9*A^2*T^4-3*A^2*T^3+8*A*T^6+5*A*T^5+T^7
  let chartK4 : ℚ → ℚ → ℚ := fun (A T : ℚ) => 3*A^3*T^3+3*A^3*T^2-3*A^3*T-A^3+9*A^2*T^4+2*A^2*T^3-5*A^2*T^2+11*A*T^5+3*A*T^4+3*T^6
  let chartK3 : ℚ → ℚ → ℚ := fun (A T : ℚ) => 3*A*T+2*A+3*T^2
  chartHomogeneous T F ((A+T)*F-A^2) A ((T+1)*F-T*A) = F^2*(chartC7 A T*F^5+chartC6 A T*F^4+A^2*T*(A*T-A+T^2)*chartK5 A T*F^3-A^4*T*(A*T-A+T^2)*chartK4 A T*F^2+A^6*T^2*(A*T-A+T^2)^2*chartK3 A T*F-A^8*T^3*(A*T-A+T^2)^2) := by sorry
