-- Prove2me | Theorems.Thm_GlobalTheory_ThetaSpecialise_move_indep
-- name    : GlobalTheory.ThetaSpecialise.move_indep
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T15:05:09.71081+00:00
-- url     : https://prove2.me/theorems/01661521-4c96-4b54-9952-16ea75368945
-- title:
--   Theta Specialise: move indep
-- statement:
--   The Theta Specialise construction uses the move indep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsMoveMap.lean#L171-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsMoveMap.lean#L171-L186

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

theorem GlobalTheory.ThetaSpecialise.move_indep (hL : L.IsLB) (hL' : L'.IsLB) (hc : ∀ κ, φ' κ ≫ Φ = h ≫ φ κ)
    (H : IsPullback h π' π (Spec.map (CommRingCat.ofHom fS))) [Flat π]
    (mv : SecOver π (LB.LinComb L φ ε) → SecOver π' (LB.LinComb L' φ' ε)) (hmv : ∀ s, PSec w φ' φ ε h (mv s) s)
    (n : ℕ) (c : Fin n → F) (hi : ∀ a : Fin n → S, ∑ i, fS (a i) * c i = 0 → ∀ i, a i = 0)
    (a : Fin n → SecOver π (LB.LinComb L φ ε)) (e : ∑ i, c i • mv (a i) = 0) (i : Fin n) : a i = 0 := by sorry
