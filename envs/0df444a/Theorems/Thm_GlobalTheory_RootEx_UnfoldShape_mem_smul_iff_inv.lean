-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_UnfoldShape_mem_smul_iff_inv
-- name    : GlobalTheory.RootEx.UnfoldShape.mem_smul_iff_inv
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:20:56.555598+00:00
-- url     : https://prove2.me/theorems/3b5212ed-22d0-4d9f-a7fc-b14e22e84953
-- title:
--   Unfold Shape: mem smul iff inv
-- statement:
--   The Unfold Shape construction uses the mem smul iff inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ScaledBasisMemChainLattice.lean#L69-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ScaledBasisMemChainLattice.lean#L69-L76

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
omit [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.RootEx.UnfoldShape.mem_smul_iff_inv {ϖ : 𝒪[k]} (h : (ϖ : k) ≠ 0) {M : Submodule 𝒪[k] (ι → k)} {v : ι → k} :
    v ∈ ϖ • M ↔ (ϖ : k)⁻¹ • v ∈ M := by sorry
