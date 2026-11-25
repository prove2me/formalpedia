-- Prove2me | Theorems.Thm_GlobalTheory_ConstFam_pullOver_injective_of_dominant
-- name    : GlobalTheory.ConstFam.pullOver_injective_of_dominant
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T15:35:59.545125+00:00
-- url     : https://prove2.me/theorems/0c095ed2-87b6-51ad-9390-4ca2298379f9
-- title:
--   Const Fam: pull Over injective of dominant
-- statement:
--   The Const Fam construction uses the pull Over injective of dominant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsSmulMemSpanOfExpandsAt.lean#L20-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsSmulMemSpanOfExpandsAt.lean#L20-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpandsAtSecIsMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpandsAtSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsFETranslateFeTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSmulMemSpanOfExpandsAt
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TopologicalSpace NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ConstFam
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.FieldBaseChange

theorem GlobalTheory.ConstFam.pullOver_injective_of_dominant {R R' : Type} [CommRing R] [CommRing R'] {X Y Y' : Scheme.{0}}
    {π : Y ⟶ Spec (CommRingCat.of R)} (L : LB X) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} (ε : K → ℤ)
    {π' : Y' ⟶ Spec (CommRingCat.of R')} {g : R →+* R'} {p : Y' ⟶ Y}
    (hp : p ≫ π = π' ≫ Spec.map (CommRingCat.ofHom g)) {φ' : K → (Y' ⟶ X)} (hφ : ∀ k, φ' k = p ≫ φ k)
    [IsSchemeTheoreticallyDominant p] [QuasiCompact p] : Function.Injective (pullOver L ε hp hφ) := by sorry
