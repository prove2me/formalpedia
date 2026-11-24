-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_UnfoldShape_mem_act_iff_inv
-- name    : GlobalTheory.RootEx.UnfoldShape.mem_act_iff_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:58.908238+00:00
-- url     : https://prove2.me/theorems/d887a071-4ab0-48b6-80e5-bcfb747e14fa
-- title:
--   Unfold Shape: mem act iff inv
-- statement:
--   The Unfold Shape construction uses the mem act iff inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ScaledBasisMemChainLattice.lean#L30-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ScaledBasisMemChainLattice.lean#L30-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_ExponentTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ScaledBasisMemChainLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.UnfoldShape
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms
variable {k : Type} [Field k] [ValuativeRel k]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
variable {k : Type} [Field k] [ValuativeRel k]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.RootEx.UnfoldShape.mem_act_iff_inv {g : GL ι k} {M : Submodule 𝒪[k] (ι → k)} {v : ι → k} :
    v ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.act g M ↔ (g⁻¹).val *ᵥ v ∈ M := by sorry
