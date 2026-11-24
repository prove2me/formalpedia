-- Prove2me | Theorems.Thm_GlobalTheory_IrredSB_mem_of_cosets
-- name    : GlobalTheory.IrredSB.mem_of_cosets
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:20:40.774826+00:00
-- url     : https://prove2.me/theorems/7a1081d4-2edb-461d-80bb-c08009716f06
-- title:
--   Irred SB: mem of cosets
-- statement:
--   The Irred SB construction uses the mem of cosets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SchwartzBruhatMatrixTranslationModulationIrreduc.lean#L65-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SchwartzBruhatMatrixTranslationModulationIrreduc.lean#L65-L94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsNeZeroOfEventually
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixIntegersModNatFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixIntegralOfAddCharTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatMatrixTranslationModulationIrreduc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel GlobalTheory.SplitWeil Matrix
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.IrredSB
variable {G : Type} [AddCommGroup G]

theorem GlobalTheory.IrredSB.mem_of_cosets (W : Submodule ℂ (G → ℂ)) (hT : ∀ Φ ∈ W, ∀ x, (fun t => Φ (t + x)) ∈ W)
    {K : AddSubgroup G} (hK : ind K ∈ W) (P : Finset G) :
    ∀ Φ : G → ℂ, (∀ u ∈ K, ∀ t, Φ (t + u) = Φ t) →
      (∀ t, Φ t ≠ 0 → ∃ s ∈ P, ∃ u ∈ K, t = s + u) → Φ ∈ W := by sorry
