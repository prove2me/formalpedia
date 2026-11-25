-- Prove2me | Theorems.Thm_GlobalTheory_ConstFam_pmaps_val
-- name    : GlobalTheory.ConstFam.pmaps_val
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:20:25.026582+00:00
-- url     : https://prove2.me/theorems/6d0b798d-907e-4301-a867-d984a46f0d6b
-- title:
--   Const Fam: pmaps val
-- statement:
--   The Const Fam construction uses the pmaps val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/LinearIndependentOfIsExtension.lean#L132-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/LinearIndependentOfIsExtension.lean#L132-L136

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

theorem GlobalTheory.ConstFam.pmaps_val (hψ : ∀ k, φ' k ≫ F = h ≫ φ k) {a : LB.Gen (LB.LinComb L' φ' ε)}
    {t : LB.Gen (LB.LinComb L φ ε)} (H : PMaps w φ' φ ε a t h) (r : Z ⟶ Y') {z : Z} {J J'} (hJ : Good L z J)
    (hJ' : Good L' z J') : val t (r ≫ h) z J = (∏ k, wVal w z J J' (r ≫ φ' k) ^ ε k) * val a r z J' := by sorry
