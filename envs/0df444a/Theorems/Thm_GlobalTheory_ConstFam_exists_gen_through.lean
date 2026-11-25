-- Prove2me | Theorems.Thm_GlobalTheory_ConstFam_exists_gen_through
-- name    : GlobalTheory.ConstFam.exists_gen_through
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:11:51.315956+00:00
-- url     : https://prove2.me/theorems/408cc2a9-1372-5769-b1e2-b1be4b531dae
-- title:
--   Const Fam: exists gen through
-- statement:
--   The Const Fam construction uses the exists gen through property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/LinearIndependentOfIsExtension.lean#L158-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/LinearIndependentOfIsExtension.lean#L158-L173

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

theorem GlobalTheory.ConstFam.exists_gen_through (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB) (hψ : ∀ k, φ' k ≫ F = h ≫ φ k)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) : ∃ a : LB.Gen (LB.LinComb L' φ' ε), a.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) J J', Good L z J → Good L' z J' →
        val t (r ≫ h) z J = (∏ k, wVal w z J J' (r ≫ φ' k) ^ ε k) * val a r z J' := by sorry
