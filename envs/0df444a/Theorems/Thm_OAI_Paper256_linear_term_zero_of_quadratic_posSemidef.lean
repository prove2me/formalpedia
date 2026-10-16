-- Prove2me | Theorems.Thm_OAI_Paper256_linear_term_zero_of_quadratic_posSemidef
-- name    : OAI.Paper256.linear_term_zero_of_quadratic_posSemidef
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T19:16:19.767578+00:00
-- url     : https://prove2.me/theorems/63f6a39f-cefc-487f-88dc-74adbb9d4993
-- title:
--   If $s^2E+sG$ is positive semidefinite for every real $s$, then $G=0$
-- statement:
--   Let $E$ and $G$ be real symmetric $n\times n$ matrices such that
--   $$s^2E+sG\succeq0\qquad\text{for every }s\in\mathbb{R},$$
--   where $\succeq0$ denotes positive semidefiniteness. Then $G=0$.
--
--   The family $s\mapsto s^2E+sG$ is a matrix-valued quadratic in $s$ without constant term; it can stay positive semidefinite for small $s$ of both signs only if the linear coefficient vanishes. The result is used to show that the parameter block $G$ of a block pencil representing the cone under study vanishes identically.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/RescalingBasic.lean#L28-L47

import Mathlib
import Definitions.Def_HyperbolicCones
import Definitions.Def_OAI_Analysis_HyperbolicCones_Model
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixLinear
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilConjugation
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_RawBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_KernelSpectrum
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilTopology
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitFrame
import Definitions.Def_OAI_Analysis_HyperbolicCones_CongruenceMaps
import Definitions.Def_OAI_Analysis_HyperbolicCones_BlockNormalization

open OAI OAI.Paper256
open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder

theorem OAI.Paper256.linear_term_zero_of_quadratic_posSemidef {n : ℕ} (E G : Sym n)
    (h : ∀ s : ℝ, (s ^ 2 • (E : Mat n ℝ) + s • (G : Mat n ℝ)).PosSemidef) :
    G = 0 := by sorry
