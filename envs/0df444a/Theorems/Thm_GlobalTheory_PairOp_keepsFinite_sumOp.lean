-- Prove2me | Theorems.Thm_GlobalTheory_PairOp_keepsFinite_sumOp
-- name    : GlobalTheory.PairOp.keepsFinite_sumOp
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:41:15.154559+00:00
-- url     : https://prove2.me/theorems/5f5bab51-61c3-40bb-8a98-98c1acc674a3
-- title:
--   Pair Op: keeps Finite sum Op
-- statement:
--   The Pair Op construction uses the keeps Finite sum Op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/PairOperatorStatement.lean#L509-L517
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/PairOperatorStatement.lean#L509-L517

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_AdjointOperatorIdentities
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsFFNeZeroThree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.AdjointOperatorIdentities
noncomputable section
open GlobalTheory GlobalTheory.PairOp
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type}
  {M : Type} [AddCommGroup M] [Module ℂ M]
variable (q : Unif k) (χ : AddChar 𝓀[k] ℂ)
variable {χ}
variable {A B A' B' : Module.End ℂ (Form k n ℂ)}

theorem GlobalTheory.PairOp.keepsFinite_sumOp (S S' : Pair k n → Finset (Pair k n)) (w : Pair k n → Pair k n → ℂ)
    (hS : ∀ P Q, Q ∈ S P → P ∈ S' Q) : KeepsFinite (sumOp S w) := by sorry
