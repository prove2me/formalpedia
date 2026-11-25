-- Prove2me | Theorems.Thm_GlobalTheory_ConstFam_sval_pullThrough
-- name    : GlobalTheory.ConstFam.sval_pullThrough
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:07:46.732811+00:00
-- url     : https://prove2.me/theorems/ed6fe946-f145-4a55-905a-b101a85dd516
-- title:
--   Const Fam: sval pull Through
-- statement:
--   The Const Fam construction uses the sval pull Through property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/LinearIndependentOfIsExtension.lean#L205-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/LinearIndependentOfIsExtension.lean#L205-L208

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_LinearIndependentOfIsExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.ConstFam
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.FieldBaseChange
variable {X X' Y Y' Z : Scheme.{0}}
variable {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]
variable {w : LB.Iso L' (L.pull F)} {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {h : Y' ⟶ Y}
variable {R R' : Type} [CommRing R] [CommRing R'] {π : Y ⟶ Spec (CommRingCat.of R)}
  {π' : Y' ⟶ Spec (CommRingCat.of R')} {f : R →+* R'}
variable (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB) (hψ : ∀ k, φ' k ≫ F = h ≫ φ k)
  (hp : h ≫ π = π' ≫ Spec.map (CommRingCat.ofHom f))

theorem GlobalTheory.ConstFam.sval_pullThrough (t : SecOver π (LB.LinComb L φ ε)) (r : Z ⟶ Y') {z : Z} {J J'} (hJ : Good L z J)
    (hJ' : Good L' z J') : sval t (r ≫ h) z J =
      (∏ k, wVal w z J J' (r ≫ φ' k) ^ ε k).val * sval (pullThrough hw hL hL' hψ ε hp t) r z J' := by sorry
