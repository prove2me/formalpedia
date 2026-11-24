-- Prove2me | Theorems.Thm_GlobalTheory_ExtDescent_isMonHom_of_grpPullback
-- name    : GlobalTheory.ExtDescent.isMonHom_of_grpPullback
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T13:16:05.487969+00:00
-- url     : https://prove2.me/theorems/0511a5c5-6e63-42d4-a69b-b074b94c4c47
-- title:
--   Ext Descent: is Mon Hom of grp Pullback
-- statement:
--   The Ext Descent construction uses the is Mon Hom of grp Pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SplitTorusExtensionDescends.lean#L26-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SplitTorusExtensionDescends.lean#L26-L49

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_RingHomFlatCodescendsAlongFaithfullyFlat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomOfFlatQuotientOfAffineKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GrpObjOfDenseOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusExtensionDescends
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ExtDescent
variable {S S₀ : Scheme.{0}} {f : S ⟶ S₀}

theorem GlobalTheory.ExtDescent.isMonHom_of_grpPullback [Flat f] [Surjective f] {X Y : Over S} {X₀ Y₀ : Over S₀}
    [GrpObj X] [GrpObj Y] [GrpObj X₀] [GrpObj Y₀] {φ : X.left ⟶ X₀.left} {ψ : Y.left ⟶ Y₀.left}
    (hX : IsGrpPullback X X₀ f φ) (hY : IsGrpPullback Y Y₀ f ψ) (g : X ⟶ Y) (g₀ : X₀ ⟶ Y₀)
    (w : φ ≫ g₀.left = g.left ≫ ψ) [IsMonHom g] : IsMonHom g₀ := by sorry
