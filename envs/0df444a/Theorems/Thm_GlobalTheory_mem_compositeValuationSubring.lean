-- Prove2me | Theorems.Thm_GlobalTheory_mem_compositeValuationSubring
-- name    : GlobalTheory.mem_compositeValuationSubring
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:16:14.357363+00:00
-- url     : https://prove2.me/theorems/16e1ec57-7459-459e-9e3a-8cdf70906cdf
-- title:
--   Global Theory: mem composite Valuation Subring
-- statement:
--   The Global Theory construction uses the mem composite Valuation Subring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsValuationSubringLeDominatingOfFractionFiel.lean#L43-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsValuationSubringLeDominatingOfFractionFiel.lean#L43-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsValuationSubringLeDominatingOfFractionFiel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory

theorem GlobalTheory.mem_compositeValuationSubring {L : Type*} [Field L] (W : ValuationSubring L)
    (V : ValuationSubring (ResidueField W)) (x : L) :
    x ∈ compositeValuationSubring W V ↔ ∃ h : x ∈ W, residue W ⟨x, h⟩ ∈ V := by sorry
