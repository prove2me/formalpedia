-- Prove2me | Theorems.Thm_GlobalTheory_splitTorus_point_eq_one_of_axes
-- name    : GlobalTheory.splitTorus_point_eq_one_of_axes
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:15:34.327593+00:00
-- url     : https://prove2.me/theorems/6dbd211d-c1a5-4ebb-baee-962e232bf669
-- title:
--   Global Theory: split Torus point eq one of axes
-- statement:
--   The Global Theory construction uses the split Torus point eq one of axes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SplitTorusPointEqOneOfAxes.lean#L13-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SplitTorusPointEqOneOfAxes.lean#L13-L27

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GeometricallyConnectedOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsMonHomPointedSplitExtToAbelianVarietyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusPointEqOneOfAxes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory

theorem GlobalTheory.splitTorus_point_eq_one_of_axes (K : Type) [Field K] [IsAlgClosed K] (E : SplitExt (Sp K))
    (G : Over (Sp K)) [GrpObj G] (h : E.IsGt G) (X : Type) [AddCommGroup X]
    (t : G ⊗ G ⟶ splitTorus (Sp K) X)
    (h₁ : lift (𝟙 G) (1 : G ⟶ G) ≫ t = 1) (h₂ : lift (1 : G ⟶ G) (𝟙 G) ≫ t = 1) : t = 1 := by sorry
