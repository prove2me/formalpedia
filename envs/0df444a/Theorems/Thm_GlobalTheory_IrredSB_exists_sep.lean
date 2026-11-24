-- Prove2me | Theorems.Thm_GlobalTheory_IrredSB_exists_sep
-- name    : GlobalTheory.IrredSB.exists_sep
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:22:33.633927+00:00
-- url     : https://prove2.me/theorems/2a514b7e-3c95-4e31-a66a-34b09394fe40
-- title:
--   Irred SB: exists sep
-- statement:
--   The Irred SB construction uses the exists sep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SchwartzBruhatMatrixTranslationModulationIrreduc.lean#L150-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SchwartzBruhatMatrixTranslationModulationIrreduc.lean#L150-L154

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
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.IrredSB.exists_sep (ψk : AddChar k Circle) (hψ : Continuous ψk) (h1 : ψk ≠ 1) {x : k} (hx : x ∉ 𝒪[k]) :
    ∃ b : k, (∀ u ∈ 𝒪[k], ψk (b * u) = 1) ∧ ψk (b * x) ≠ 1 := by sorry
