-- Prove2me | Theorems.Thm_OAI_Cotype_operatorWalsh_L2_lipschitz
-- name    : OAI.Cotype.operatorWalsh_L2_lipschitz
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T19:50:21.605328+00:00
-- url     : https://prove2.me/theorems/be8f7422-2b06-4d76-abda-a7318bb830b6
-- title:
--   The Walsh transform is Lipschitz in the operator
-- statement:
--   Let $X,Y$ be real normed spaces and $f:\{0,1\}^n\to X$. For an operator $A:X\to Y$, let $W_Af(v)=\mathbb E_u\chi_v(u)\,Af(u)$ be the Walsh transform of $Af$, and $\|g\|_{L_2}=(\mathbb E\|g\|^2)^{1/2}$ with $\mathbb E$ the uniform average. Then for operators $A,B:X\to Y$,
--   $$
--   \bigl|\,\|W_Af\|_{L_2}-\|W_Bf\|_{L_2}\bigr|\le\|A-B\|\,\|f\|_{L_2}.
--   $$
--
--   The size of the Walsh transform moves continuously with the operator.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/VectorWalsh.lean#L124-L137

import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
import Definitions.Def_OAI_Analysis_Cotype_VectorWalsh

open OAI OAI.Cotype
open scoped BigOperators
open WithLp
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem OAI.Cotype.operatorWalsh_L2_lipschitz {n : ℕ} (A B : X →L[ℝ] Y) (f : Cube n → X) :
    |cubeL2 Y (operatorWalsh A f) - cubeL2 Y (operatorWalsh B f)| ≤ ‖A-B‖ * cubeL2 X f := by sorry
