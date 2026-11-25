-- Prove2me | Theorems.Thm_GlobalTheory_WeightTwo_formEq_cancel
-- name    : GlobalTheory.WeightTwo.formEq_cancel
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:10:50.135425+00:00
-- url     : https://prove2.me/theorems/8613f73b-b044-40b3-b06f-e6659494f89b
-- title:
--   Weight Two: form Eq cancel
-- statement:
--   The Weight Two construction uses the form Eq cancel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsSecFinsum.lean#L34-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsSecFinsum.lean#L34-L72

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqZeroOfThickeningsOfSection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalEqZeroOfSumMulCoord
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_StalkMapInjectiveOfFlat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecFinsum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory GlobalTheory.WeightTwo
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)

theorem GlobalTheory.WeightTwo.formEq_cancel (k l : ℕ) (α β : D.X) :
    FormEq (Sum.elim (fun a => (D.P.A ◁ g.pG).left ≫ Sum.elim (fun i => (fst D.P.A D.P.A).left ≫ D.famφB α i)
        (fun i => (snd D.P.A D.P.A).left ≫ D.famφB β i) a)
        (fun a => (snd D.P.A ((Over.map (thick R I e)).obj (thickObj R I e G))).left ≫ D.Oφ g.pG β a))
      (Sum.elim (Sum.elim (DegPre.famε k) (DegPre.famε l)) Oinvε)
      (Sum.elim (fun i => (fst D.P.A ((Over.map (thick R I e)).obj (thickObj R I e G))).left ≫ D.famφB α i)
        (fun _ : Unit => (snd D.P.A _ ≫ g.pG).left))
      (Sum.elim (DegPre.famε k) (fun _ => (l : ℤ))) := by sorry
