-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_UnfoldShape_mem_perLat
-- name    : GlobalTheory.RootEx.UnfoldShape.mem_perLat
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:35:32.242509+00:00
-- url     : https://prove2.me/theorems/5f0f3ba1-d343-40ef-b246-50cb1df98f45
-- title:
--   Unfold Shape: mem per Lat
-- statement:
--   The Unfold Shape construction uses the mem per Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ScaledBasisMemChainLattice.lean#L476-L478
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ScaledBasisMemChainLattice.lean#L476-L478

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
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k]
omit [MeasurableSpace k] [BorelSpace k]

theorem GlobalTheory.RootEx.UnfoldShape.mem_perLat {ϖ : 𝒪[k]} {L : Submodule 𝒪[k] (n → k)}
    {e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free 1 rs} → k} :
    e ∈ perLat ϖ n' c L ↔ ∀ i : Fin c, (ϖ : k) ^ (i.val + 1) • col e i ∈ chainLat ϖ c L := by sorry
