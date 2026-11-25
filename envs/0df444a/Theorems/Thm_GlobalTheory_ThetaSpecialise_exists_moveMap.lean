-- Prove2me | Theorems.Thm_GlobalTheory_ThetaSpecialise_exists_moveMap
-- name    : GlobalTheory.ThetaSpecialise.exists_moveMap
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T15:03:49.86581+00:00
-- url     : https://prove2.me/theorems/f8ec4dd0-1a6c-40d2-9c70-4e146de0b2c2
-- title:
--   Theta Specialise: exists move Map
-- statement:
--   The Theta Specialise construction uses the exists move Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsMoveMap.lean#L151-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsMoveMap.lean#L151-L169

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExpansionBijectiveOverFields
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsAtTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PowEqOneOfPush
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ThetaGrpActsLinearly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsMoveMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaSpecialise
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange
variable {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {Φ : X' ⟶ X} {K : Type} [Fintype K]
variable {w : LB.Iso L' (L.pull Φ)} {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {h : Y' ⟶ Y}
  {S F : Type} [CommRing S] [CommRing F] {fS : S →+* F}
  {π : Y ⟶ Spec (CommRingCat.of S)} {π' : Y' ⟶ Spec (CommRingCat.of F)}

theorem GlobalTheory.ThetaSpecialise.exists_moveMap (hL : L.IsLB) (hL' : L'.IsLB) (hw : w.IsGen) (hc : ∀ κ, φ' κ ≫ Φ = h ≫ φ κ)
    (hp : h ≫ π = π' ≫ Spec.map (CommRingCat.ofHom fS)) :
    ∃ mv : SecOver π (LB.LinComb L φ ε) →ₛₗ[fS] SecOver π' (LB.LinComb L' φ' ε),
      ∀ s s', PSec w φ' φ ε h s' s ↔ mv s = s' := by sorry
