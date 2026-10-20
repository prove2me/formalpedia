-- Prove2me | Theorems.Thm_OAI_Cotype_exists_dualPairing_norming
-- name    : OAI.Cotype.exists_dualPairing_norming
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T19:52:07.190311+00:00
-- url     : https://prove2.me/theorems/b93d77d6-baa6-40eb-ba12-00509d678827
-- title:
--   Norming dual functions for the cube L2 norm
-- statement:
--   Let $X$ be a real normed space and $f:\{0,1\}^n\to X$. There is a function $g:\{0,1\}^n\to X^*$ with $\|g\|_{L_2}\le1$ and
--   $$
--   \mathbb E_u\,g(u)\bigl(f(u)\bigr)=\|f\|_{L_2},
--   $$
--   where $\|h\|_{L_2}=(\mathbb E\|h\|^2)^{1/2}$ and $\mathbb E$ is the uniform average.
--
--   So the $L_2(X)$ norm on the cube is attained by pairing with $L_2(X^*)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/WalshDuality.lean#L48-L74

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

theorem OAI.Cotype.exists_dualPairing_norming {n : ℕ} (f : Cube n → X) :
    ∃ g : Cube n → (X →L[ℝ] ℝ), cubeL2 (X →L[ℝ] ℝ) g ≤ 1 ∧
      dualPairing f g = cubeL2 X f := by sorry
