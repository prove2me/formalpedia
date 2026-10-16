-- Prove2me | Theorems.Thm_OAI_Paper256_posSemidef_three_of_principal_minors
-- name    : OAI.Paper256.posSemidef_three_of_principal_minors
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T19:07:18.263337+00:00
-- url     : https://prove2.me/theorems/e878aa1b-5c24-4ebe-afb6-5e2072ca6b77
-- title:
--   Nonnegative principal minors certify positive semidefiniteness of a symmetric $3\times3$ matrix
-- statement:
--   Let $M=(m_{ij})_{i,j=1}^{3}$ be a real symmetric $3\times3$ matrix whose principal minors are all nonnegative, namely
--   $$m_{11},\,m_{22},\,m_{33}\ge0,\qquad m_{12}^2\le m_{11}m_{22},\quad m_{13}^2\le m_{11}m_{33},\quad m_{23}^2\le m_{22}m_{33},\qquad \det M\ge0 .$$
--   Then $M$ is positive semidefinite: $v^\top Mv\ge0$ for every $v\in\mathbb{R}^3$.
--
--   This is the $3\times3$ case of the criterion that a real symmetric matrix is positive semidefinite exactly when all of its principal minors (not only the leading ones) are nonnegative. In the surrounding development it is applied to an explicit $3\times3$ matrix whose quadratic form is the Choi–Lam form, which yields nonnegativity of that form.
--
--   **Formalization Note** Lean indexes rows and columns by $0,1,2$; the three $2\times2$ minor conditions are stated entrywise as `M 0 1 ^ 2 ≤ M 0 0 * M 1 1` and so on, and symmetry is the hypothesis `M.IsHermitian`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/FormPositive.lean#L69-L88

import Mathlib
import Definitions.Def_HyperbolicCones
import Definitions.Def_OAI_Analysis_HyperbolicCones_Model
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixLinear
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilConjugation
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_RawBlocks

open OAI OAI.Paper256
open scoped Matrix.Norms.L2Operator
open Matrix

theorem OAI.Paper256.posSemidef_three_of_principal_minors (M : Mat 3 ℝ) (hM : M.IsHermitian)
    (hdiag : ∀ i, 0 ≤ M i i)
    (h01 : M 0 1 ^ 2 ≤ M 0 0 * M 1 1)
    (h02 : M 0 2 ^ 2 ≤ M 0 0 * M 2 2)
    (h12 : M 1 2 ^ 2 ≤ M 1 1 * M 2 2) (hdet : 0 ≤ Matrix.det M) :
    M.PosSemidef := by sorry
