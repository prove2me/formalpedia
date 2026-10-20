-- Prove2me | Theorems.Thm_OAI_Cotype_cubeNoise_norm_le
-- name    : OAI.Cotype.cubeNoise_norm_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T19:53:23.124204+00:00
-- url     : https://prove2.me/theorems/e940ca00-3af1-4399-9f25-d6dcf3a996ac
-- title:
--   The cube noise operator is dominated by its action on norms
-- statement:
--   Let $X$ be a real normed space. On functions $f:\{0,1\}^n\to X$ let $N$ be the noise operator that keeps each coordinate with probability $\frac34$ and flips it with probability $\frac14$, independently:
--   $$
--   Nf(u)=\sum_v\prod_i\bigl(\tfrac34\mathbf 1_{v_i=u_i}+\tfrac14\mathbf 1_{v_i\ne u_i}\bigr)f(v).
--   $$
--   Then $\|Nf(u)\|\le N(\|f\|)(u)$ for every $u$.
--
--   The noise operator averages with nonnegative weights, so the norm of the average is at most the average of the norms.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/CubeNoise.lean#L69-L85

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
import Definitions.Def_OAI_Analysis_Cotype_CubeNoise

open OAI OAI.Cotype
open scoped BigOperators
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem OAI.Cotype.cubeNoise_norm_le {n : ℕ} (f : Cube n → X) (u : Cube n) :
    ‖cubeNoise f u‖ ≤ cubeNoise (fun v => ‖f v‖) u := by sorry
