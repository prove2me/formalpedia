-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_spherical_quadraticIndependent_ramsey
-- name    : OAI.EuclideanRamsey.spherical_quadraticIndependent_ramsey
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T12:33:37.064112+00:00
-- url     : https://prove2.me/theorems/0475e91f-b58f-47ee-891a-70a06cbcd8fb
-- title:
--   Spherical configurations with independent quadratic rows are Ramsey
-- statement:
--   Let $a_0,\dots,a_{s-1}\in\mathbb R^d$ with $s>0$ be distinct and affinely spanning $\mathbb R^d$, and suppose they lie on a sphere. Let $K$ be their coordinate field and $\tilde a_i=(1,a_{i1},\dots,a_{id})$. If the quadratic rows $\bigl(\tilde a_i(p)\tilde a_i(q)\bigr)_{p,q}$ are linearly independent over $K$, then
--   $$
--   a\ \text{is Ramsey}.
--   $$
--
--   This sufficient condition is the route by which small spherical configurations are shown to be Ramsey.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/Quadratic.lean#L220-L241

import Mathlib
import Definitions.Def_EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Model__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CircleInterpolation
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CircleRows
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CircleExtension
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingMatrix__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Discretization__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_AdicLifting__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorPresentation__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SignedRows__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_FiniteEuclidean__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathFractions__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DerivedFractions__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathWords__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_UltrafilterStrings__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathSynchronization__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CornerGroup__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_ColoringCompactness__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_NormalCost__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_OrbitAveraging__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CorrectionPaths__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Quadratic__EuclideanRamseyCircle

open OAI OAI.EuclideanRamsey
open scoped TensorProduct BigOperators RealInnerProductSpace Matrix

theorem OAI.EuclideanRamsey.spherical_quadraticIndependent_ramsey {s d : ℕ} (a : Fin s → Space d)
    (hs : 0 < s) (ha : Function.Injective a)
    (hspan : affineSpan ℝ (Set.range a) = ⊤)
    (hsphere : ∃ c : Space d, ∃ r : ℝ, ∀ i, dist (a i) c = r)
    (hrows : LinearIndependent (Coeff a)
      (fun i : Fin s => fun q : Option (Fin d) × Option (Fin d) =>
        augmented a i q.1 * augmented a i q.2)) : Ramsey a := by sorry
