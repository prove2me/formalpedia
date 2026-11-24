-- Prove2me | Theorems.Thm_GlobalTheory_PairOp_dia_unitary
-- name    : GlobalTheory.PairOp.dia_unitary
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:43:51.606318+00:00
-- url     : https://prove2.me/theorems/1e374db2-9b44-4672-b510-336e70f98b0c
-- title:
--   Pair Op: dia unitary
-- statement:
--   The Pair Op construction uses the dia unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/PairOperatorStatement.lean#L610-L620
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/PairOperatorStatement.lean#L610-L620

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

theorem GlobalTheory.PairOp.dia_unitary {W : Submodule ℂ (Form k n ℂ)} (hW : ∀ c : 𝓀[k]ˣ, ∀ φ ∈ W, dia c φ ∈ W) (c : 𝓀[k]ˣ) :
    IsScaledUnitaryOn W 1 (dia c) := by sorry
