-- Prove2me | Theorems.Thm_GlobalTheory_GodementJacquet_TestNearE_nhds_zero_basis
-- name    : GlobalTheory.GodementJacquet.TestNearE.nhds_zero_basis
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T13:57:17.340292+00:00
-- url     : https://prove2.me/theorems/42779c96-20c7-4f06-be08-92277525e124
-- title:
--   Test Near E: nhds zero basis
-- statement:
--   The Test Near E construction uses the nhds zero basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsSchwartzBumpNearIdentity.lean#L74-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsSchwartzBumpNearIdentity.lean#L74-L86

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_LeviRep
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsSchwartzBumpNearIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GodementJacquet MeasureTheory
open GlobalTheory GlobalTheory.GodementJacquet GlobalTheory.GodementJacquet.TestNearE
open ValuativeRel Filter Topology

theorem GlobalTheory.GodementJacquet.TestNearE.nhds_zero_basis (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n m : ℕ) : (𝓝 (0 : Matrix (Fin n) (Fin m) k)).HasBasis
      (fun IJ : Set (Fin n) × (Set (Fin m) × (ValueGroupWithZero k)ˣ) => IJ.1.Finite ∧ (IJ.2.1.Finite ∧ True))
      (fun IJ => IJ.1.pi fun _ => IJ.2.1.pi fun _ => {x : k | valuation k x < IJ.2.2}) := by sorry
