-- Prove2me | Theorems.Thm_GlobalTheory_QkPairing_exists_const
-- name    : GlobalTheory.QkPairing.exists_const
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:09:12.383877+00:00
-- url     : https://prove2.me/theorems/64ec01ce-e636-409f-a487-4c81fcfddf3f
-- title:
--   Qk Pairing: exists const
-- statement:
--   The Qk Pairing construction uses the exists const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/WeilQkPairingExistsUniqueTorus.lean#L54-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/WeilQkPairingExistsUniqueTorus.lean#L54-L69

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ClosedPointWeilPower
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsUniqueFamOfReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_WeilQkPairingExistsUniqueTorus
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_exists_const

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
noncomputable section
open GlobalTheory GlobalTheory.QkPairing

theorem GlobalTheory.QkPairing.exists_const {X : Scheme.{0}} {M : LB X} (hM : M.IsLB) {F : Type} [Field F] {K : Type} [Fintype K]
    {φ : K → (Spec (CommRingCat.of F) ⟶ X)} {ε : K → ℤ} (u : LB.Gen (LB.LinComb M φ ε)) (hu : u.IsGen)
    (hF : ∀ (U : Type) [CommGroup U] (h : (Spec (CommRingCat.of F) ⟶ X) → U), ∏ k, h (φ k) ^ ε k = 1) :
    ∃ ζ : Fˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of F)) (z : Z) (J), Good M z J →
      (val u r z J).val = gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ζ.val) := by sorry
