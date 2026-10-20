-- Prove2me | Theorems.Thm_OAI_Cotype_average_norm_mul_le
-- name    : OAI.Cotype.average_norm_mul_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T19:51:28.353118+00:00
-- url     : https://prove2.me/theorems/5427ae8b-d80c-4bfe-b50f-616ecd9e4db2
-- title:
--   Cauchy–Schwarz for averaged products of norms on the cube
-- statement:
--   Let $X,Y$ be normed groups and $f:\{0,1\}^n\to X$, $g:\{0,1\}^n\to Y$. Then
--   $$
--   \mathbb E_u\,\|f(u)\|\,\|g(u)\|\le\bigl(\mathbb E\|f\|^2\bigr)^{1/2}\bigl(\mathbb E\|g\|^2\bigr)^{1/2},
--   $$
--   where $\mathbb E$ is the uniform average over the cube.
--
--   This is the Cauchy–Schwarz inequality for the normalized counting measure.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/WalshDuality.lean#L13-L28

import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
import Definitions.Def_OAI_Analysis_Cotype_VectorWalsh
import Definitions.Def_OAI_Analysis_Cotype_WalshNorm
import Definitions.Def_OAI_Analysis_Cotype_WalshCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshDuality

open OAI OAI.Cotype
open scoped BigOperators
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

omit [NormedSpace ℝ X] [NormedSpace ℝ Y] in
theorem OAI.Cotype.average_norm_mul_le {n : ℕ} (f : Cube n → X) (g : Cube n → Y) :
    average (fun u => ‖f u‖ * ‖g u‖) ≤ cubeL2 X f * cubeL2 Y g := by sorry
