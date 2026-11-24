-- Prove2me | Theorems.Thm_GlobalTheory_KernelComm_sum_target
-- name    : GlobalTheory.KernelComm.sum_target
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:12:44.245404+00:00
-- url     : https://prove2.me/theorems/9716ff4e-6de7-40b0-a5dc-830f4e5a0c12
-- title:
--   Kernel Comm: sum target
-- statement:
--   The Kernel Comm construction uses the sum target property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IndicatorIdentity.lean#L21-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IndicatorIdentity.lean#L21-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_IndicatorFunctionIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IndicatorIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity GlobalTheory.PairOp
noncomputable section
open GlobalTheory GlobalTheory.KernelComm
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type}
variable [Fintype n'] (q : Unif k) {P₁ : Pair k n'} {e₁ : n' → k} (he : P₁.HasVal e₁ 1) (Q : Pair k n)
  (x : Matrix n n' k)
include he
open Classical

theorem GlobalTheory.KernelComm.sum_target :
    ∑ Q₁ ∈ withKer Q.lat with cross q Q₁ Q = 1, phiOne P₁ Q₁ x = midInd q P₁.ker e₁ Q x := by sorry
