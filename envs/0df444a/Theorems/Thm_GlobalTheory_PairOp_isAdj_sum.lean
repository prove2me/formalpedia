-- Prove2me | Theorems.Thm_GlobalTheory_PairOp_isAdj_sum
-- name    : GlobalTheory.PairOp.isAdj_sum
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:41:11.667194+00:00
-- url     : https://prove2.me/theorems/5fd257f3-52d2-4e5c-a456-79b704237c9f
-- title:
--   Pair Op: is Adj sum
-- statement:
--   The Pair Op construction uses the is Adj sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/PairOperatorStatement.lean#L578-L588
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/PairOperatorStatement.lean#L578-L588

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

theorem GlobalTheory.PairOp.isAdj_sum {ι : Type} (s : Finset ι) (a b : ι → ℂ) (A B : ι → Module.End ℂ (Form k n ℂ))
    (hab : ∀ i, (starRingEnd ℂ) (b i) = a i) (h : ∀ i, IsAdj (A i) (B i)) :
    IsAdj (∑ i ∈ s, a i • A i) (∑ i ∈ s, b i • B i) := by sorry
