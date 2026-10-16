-- Prove2me | Theorems.Thm_OAI_Paper256_posSemidef_norm_threshold
-- name    : OAI.Paper256.posSemidef_norm_threshold
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T19:44:18.395375+00:00
-- url     : https://prove2.me/theorems/b0fc76c0-bdd5-456c-ad1b-1eb5eec2b2a3
-- title:
--   For positive semidefinite $A$, $rI-A\succeq0$ holds exactly when $\|A\|\le r$
-- statement:
--   Let $n\ge1$, let $A\in\mathbb{R}^{n\times n}$ be positive semidefinite (symmetric with $x^{\mathsf T}Ax\ge0$ for all $x\in\mathbb{R}^n$), and let $r\in\mathbb{R}$. Write $\|A\|=\max_{\|x\|=1}\|Ax\|$ for the operator norm of $A$ induced by the Euclidean norm (the spectral norm). Then
--   $$
--   rI_n-A\succeq0\quad\Longleftrightarrow\quad\|A\|\le r .
--   $$
--
--   For positive semidefinite $A$ the spectral norm is the largest eigenvalue, so the theorem says that $\|A\|$ is the smallest scalar $r$ with $A\preceq rI_n$. It is a convenient way to convert matrix inequalities of the form $A\preceq rI$ into operator-norm bounds and back.
--
--   **Formalization Note** The assumption $n\ge1$ is the instance `[NeZero n]`. It is needed: for $n=0$ one has $\|A\|=0$, while $rI-A\succeq0$ holds for every $r$. The norm is the scoped instance `Matrix.Norms.L2Operator`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/NormThreshold.lean#L22-L35

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
import Definitions.Def_OAI_Analysis_HyperbolicCones_Coordinates
import Definitions.Def_OAI_Analysis_HyperbolicCones_ConeMatrix
import Definitions.Def_OAI_Analysis_HyperbolicCones_GramProjection
import Definitions.Def_OAI_Analysis_HyperbolicCones_KernelSmooth
import Definitions.Def_OAI_Analysis_HyperbolicCones_TangentBasic

open OAI OAI.Paper256
open scoped Matrix.Norms.L2Operator MatrixOrder
open Matrix

theorem OAI.Paper256.posSemidef_norm_threshold {n : ℕ} [NeZero n] (A : Mat n ℝ)
    (hA : A.PosSemidef) (r : ℝ) :
    (r • (1 : Mat n ℝ) - A).PosSemidef ↔ ‖A‖ ≤ r := by sorry
