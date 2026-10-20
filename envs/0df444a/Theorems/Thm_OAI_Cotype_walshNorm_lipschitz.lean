-- Prove2me | Theorems.Thm_OAI_Cotype_walshNorm_lipschitz
-- name    : OAI.Cotype.walshNorm_lipschitz
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T19:50:53.466689+00:00
-- url     : https://prove2.me/theorems/f7c17696-90e5-43d7-a9a0-e4b49187036d
-- title:
--   The Walsh norm is 1-Lipschitz in the operator norm
-- statement:
--   Let $X,Y$ be real normed spaces and $n\in\mathbb N$. For $A:X\to Y$ let
--   $$
--   \omega_n(A)=\sup\bigl\{\|W_Af\|_{L_2}:\ f:\{0,1\}^n\to X,\ \|f\|_{L_2}\le1\bigr\}
--   $$
--   be the Walsh norm, where $W_Af$ is the Walsh transform of $Af$. Then $|\omega_n(A)-\omega_n(B)|\le\|A-B\|$ for all $A,B:X\to Y$.
--
--   In particular the Walsh norm is continuous on the space of operators.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/WalshNorm.lean#L70-L83

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

open OAI OAI.Cotype
open scoped BigOperators
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem OAI.Cotype.walshNorm_lipschitz (n : ℕ) (A B : X →L[ℝ] Y) :
    |walshNorm n A - walshNorm n B| ≤ ‖A-B‖ := by sorry
