-- Prove2me | Theorems.Thm_OAI_Paper256_fromBlocks_add_lower_posDef
-- name    : OAI.Paper256.fromBlocks_add_lower_posDef
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T19:20:21.459889+00:00
-- url     : https://prove2.me/theorems/83fdedf0-7ad9-4fd4-8aa5-0e6c5856af2e
-- title:
--   Shifting the lower-right block by $\delta I$ makes a positive semidefinite block matrix with positive definite corner positive definite
-- statement:
--   Let $A$ be a real symmetric $a\times a$ matrix, $E$ a real symmetric $c\times c$ matrix and $B$ a real $a\times c$ matrix. Write $\succeq0$ for positive semidefiniteness and $\succ0$ for positive definiteness. Suppose $A\succ0$ and
--   $$\begin{pmatrix}A&B\\B^\top&E\end{pmatrix}\succeq0 .$$
--   Then for every $\delta>0$
--   $$\begin{pmatrix}A&B\\B^\top&E+\delta I_c\end{pmatrix}\succ0 .$$
--
--   This regularization upgrades positive semidefiniteness to positive definiteness by a small shift of the lower-right block. Since positive definiteness is an open condition, the shifted matrix can then be perturbed, which is used when recovering the slice condition from a limiting block matrix.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/StrictBlock.lean#L23-L56

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
import Definitions.Def_OAI_Analysis_HyperbolicCones_BlockReduction
import Definitions.Def_OAI_Analysis_HyperbolicCones_ScalingAlgebra
import Definitions.Def_OAI_Analysis_HyperbolicCones_FiniteTopology
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilLimit

open OAI OAI.Paper256
open Matrix
open scoped Matrix.Norms.L2Operator
universe u v

theorem OAI.Paper256.fromBlocks_add_lower_posDef {a c : ℕ} (A : Sym a) (E : Sym c)
    (B : Matrix (Fin a) (Fin c) ℝ) (hA : (A : Mat a ℝ).PosDef)
    (hM : (Matrix.fromBlocks (A : Mat a ℝ) B Bᵀ (E : Mat c ℝ)).PosSemidef)
    (δ : ℝ) (hδ : 0 < δ) :
    (Matrix.fromBlocks (A : Mat a ℝ) B Bᵀ ((E : Mat c ℝ) + δ • 1)).PosDef := by sorry
