-- Prove2me | Theorems.Thm_OAI_Paper256_posSemidef_of_nonsingular_path
-- name    : OAI.Paper256.posSemidef_of_nonsingular_path
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T19:27:50.207984+00:00
-- url     : https://prove2.me/theorems/9c3dee3d-01b9-48b5-a060-d7220e388e05
-- title:
--   A symmetric matrix path that is nonsingular for $t>0$ and somewhere positive definite is positive semidefinite at $0$
-- statement:
--   Let $n\ge0$ and let $\mathrm{Sym}_n$ denote the space of real symmetric $n\times n$ matrices with its usual topology. A matrix $M\in\mathrm{Sym}_n$ is positive semidefinite ($M\succeq0$) if $v^{\mathsf T}Mv\ge0$ for all $v\in\mathbb{R}^n$, and positive definite ($M\succ0$) if $v^{\mathsf T}Mv>0$ for all $v\ne0$. Let $F:\mathbb{R}\to\mathrm{Sym}_n$ satisfy
--
--   1. $F$ is continuous on $[0,\infty)$, and $F$ is continuous at $0$;
--   2. $F(t)$ is invertible for every $t>0$;
--   3. there is some $t_0>0$ with $F(t_0)\succ0$.
--
--   Then
--   $$
--   F(0)\succeq0 .
--   $$
--
--   A continuous path of symmetric matrices can change its inertia only by passing through a singular matrix. So a path that is nonsingular for all positive times and positive definite at one of them stays positive definite on $(0,\infty)$, and its starting value is a limit of positive definite matrices. This is the topological step used to deduce positive semidefiniteness of a matrix at $t=0$ from the nonvanishing of a determinant along a shifted line.
--
--   **Formalization Note** The path has type `ℝ → Sym n`, where `Sym n` is the subtype of self-adjoint real matrices. Hypothesis 1 consists of `ContinuousOn F (Ici 0)` and the two-sided `ContinuousAt F 0`; invertibility is `IsUnit`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/PositivePath.lean#L12-L45

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

open OAI OAI.Paper256
open Set Filter Matrix
open scoped Topology Matrix.Norms.L2Operator

theorem OAI.Paper256.posSemidef_of_nonsingular_path {n : ℕ} (F : ℝ → Sym n)
    (hF : ContinuousOn F (Ici 0)) (hF0 : ContinuousAt F 0)
    (hunit : ∀ t : ℝ, 0 < t → IsUnit (F t : Mat n ℝ))
    (hpos : ∃ t : ℝ, 0 < t ∧ (F t : Mat n ℝ).PosDef) :
    (F 0 : Mat n ℝ).PosSemidef := by sorry
