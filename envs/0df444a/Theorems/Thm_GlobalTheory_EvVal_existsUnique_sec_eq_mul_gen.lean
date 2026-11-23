-- Prove2me | Theorems.Thm_GlobalTheory_EvVal_existsUnique_sec_eq_mul_gen
-- name    : GlobalTheory.EvVal.existsUnique_sec_eq_mul_gen
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:52:47.779862+00:00
-- url     : https://prove2.me/theorems/93a4bf4d-9876-44c3-8b5a-d3e495778dc8
-- title:
--   Ev Val: exists Unique sec eq mul gen
-- statement:
--   The Ev Val construction uses the exists Unique sec eq mul gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsUniqueSecEqMulGen.lean#L15-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsUniqueSecEqMulGen.lean#L15-L28

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueSecEqMulGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.EvVal

theorem GlobalTheory.EvVal.existsUnique_sec_eq_mul_gen {Y : Scheme.{0}} (M : LB Y) (hc : ⨆ j, M.U j = ⊤)
    (s : LB.Sec M) (t : LB.Gen M) (ht : t.IsGen) :
    ∃! v : Γ(Y, ⊤), ∀ j, s.f j =
      (Y.presheaf.map (homOfLE (le_top : M.U j ≤ ⊤)).op).hom v * (t.s j).val := by sorry
