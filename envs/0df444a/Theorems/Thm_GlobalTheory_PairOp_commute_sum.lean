-- Prove2me | Theorems.Thm_GlobalTheory_PairOp_commute_sum
-- name    : GlobalTheory.PairOp.commute_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:47.308888+00:00
-- url     : https://prove2.me/theorems/c13750f3-caab-450a-b834-24cfd0043c7d
-- title:
--   Pair Op: commute sum
-- statement:
--   The Pair Op construction uses the commute sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/PairOperatorStatement.lean#L170-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/PairOperatorStatement.lean#L170-L175

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

theorem GlobalTheory.PairOp.commute_sum {A : Module.End ℂ (Form k n M)} (h : ∀ c : 𝓀[k]ˣ, A * dia c = dia c * A) {ι : Type}
    (s : Finset ι) (a : ι → ℂ) (e : ι → 𝓀[k]ˣ) :
    A * (∑ i ∈ s, a i • dia (e i)) = (∑ i ∈ s, a i • dia (e i)) * A := by sorry
