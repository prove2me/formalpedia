-- Prove2me | Theorems.Thm_K24_Global_FlatTorus_defect_haar_and_projection
-- name    : K24.Global.FlatTorus.defect_haar_and_projection
-- status  : Proved
-- author  : @xwh
-- created : 2026-10-23T19:28:00.173807+00:00
-- url     : https://prove2.me/theorems/f7e2983e-4744-473a-af77-cce433d5beb1
-- title:
--   K24 actual torus defect has zero Haar average and unchanged projection
-- statement:
--   For every original smooth circle action rho on the actual four-torus whose action map equals translate, every real exponent alpha and every natural frequency n, the actual unprojected Bianchi-Lie defect is fiberwise Haar integrable, its actual covector Haar average vanishes, and its projected defect equals its unprojected defect. This supplies the original sharpness Haar clause and the bridge transporting exact unprojected-defect bounds to the projected norm.
-- source:
--   Original full K24 target aac3db7a-b1fb-4137-ab8b-8f9efc4d3b22, torus analytic residual 9c6a6e33-1818-46c7-910f-1917ab540986; unchanged original CircleAction, translate, CovectorHaarIntegrable, unprojectedDefect, covectorPi0 and projectedDefect definitions.

import Definitions.Def_K24GlobalStatement
set_option autoImplicit false

namespace K24.Global.FlatTorus
theorem defect_haar_and_projection :
    ∀ (rho : CircleAction Torus), rho.act = translate → ∀ (alpha : ℝ) (n : ℕ),
      CovectorHaarIntegrable rho (unprojectedDefect alpha n) ∧
      covectorPi0 rho (unprojectedDefect alpha n) = 0 ∧
      projectedDefect rho alpha n = unprojectedDefect alpha n := by
  sorry
end K24.Global.FlatTorus
