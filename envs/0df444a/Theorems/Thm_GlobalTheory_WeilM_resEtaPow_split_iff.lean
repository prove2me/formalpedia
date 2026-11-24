-- Prove2me | Theorems.Thm_GlobalTheory_WeilM_resEtaPow_split_iff
-- name    : GlobalTheory.WeilM.resEtaPow_split_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:54:50.716357+00:00
-- url     : https://prove2.me/theorems/6311932a-737b-4d8d-b605-03d8bc9ce22b
-- title:
--   Weil M: res Eta Pow split iff
-- statement:
--   The Weil M construction uses the res Eta Pow split iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeilObjectsInhabited.lean#L219-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeilObjectsInhabited.lean#L219-L224

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSplittingSplitOm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompactOpenAddSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeilObjectsInhabited
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ValuativeRel
open scoped NNReal Topology Kronecker
open GlobalTheory GlobalTheory.WeilM
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {α β κ : Type}
variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] [Invertible (2 : F)]
variable {R : Type} [CommRing R]

theorem GlobalTheory.WeilM.resEtaPow_split_iff (χ : (R × R)ˣ →* Circle) (n : ℕ) :
    ResEtaPow (⊥ : Subgroup Rˣ) χ n ↔ ∀ a : Rˣ, χ (Units.map (algebraMap R (R × R) : R →* R × R) a) = 1 := by sorry
