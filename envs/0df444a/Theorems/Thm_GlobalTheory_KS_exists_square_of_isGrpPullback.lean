-- Prove2me | Theorems.Thm_GlobalTheory_KS_exists_square_of_isGrpPullback
-- name    : GlobalTheory.KS.exists_square_of_isGrpPullback
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:46:21.799326+00:00
-- url     : https://prove2.me/theorems/365bee37-44cb-4895-998a-7adf0498967f
-- title:
--   KS: exists square of is Grp Pullback
-- statement:
--   The KS construction uses the exists square of is Grp Pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSquareOfIsGrpPullback.lean#L15-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSquareOfIsGrpPullback.lean#L15-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSquareOfIsGrpPullback
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.KS

theorem GlobalTheory.KS.exists_square_of_isGrpPullback {S S' : Scheme.{0}} (G' : Over S') [GrpObj G'] (G : Over S)
    [GrpObj G] (f : S' ⟶ S) (m : G'.left ⟶ G.left) (h : IsGrpPullback G' G f m) :
    ∃ m₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left, ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsSquare m m₂ ∧
      m₂ ≫ (fst G G * snd G G).left = (fst G' G' * snd G' G').left ≫ m ∧
      m₂ ≫ (G ⊗ G).hom = (G' ⊗ G').hom ≫ f := by sorry
