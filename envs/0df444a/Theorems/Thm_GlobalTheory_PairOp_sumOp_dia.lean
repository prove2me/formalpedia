-- Prove2me | Theorems.Thm_GlobalTheory_PairOp_sumOp_dia
-- name    : GlobalTheory.PairOp.sumOp_dia
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:59.077806+00:00
-- url     : https://prove2.me/theorems/8f32d9c6-ab80-4bad-9345-873af3952d6f
-- title:
--   Pair Op: sum Op dia
-- statement:
--   The Pair Op construction uses the sum Op dia property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/PairOperatorStatement.lean#L129-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/PairOperatorStatement.lean#L129-L137

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

theorem GlobalTheory.PairOp.sumOp_dia (S : Pair k n → Finset (Pair k n)) (w : Pair k n → Pair k n → ℂ) (c : 𝓀[k]ˣ)
    (hS : ∀ P Q, Q ∈ S P ↔ c • Q ∈ S (c • P)) (hw : ∀ P, ∀ Q ∈ S P, w (c • P) (c • Q) = w P Q) :
    (sumOp S w * dia c : Module.End ℂ (Form k n M)) = dia c * sumOp S w := by sorry
