-- Prove2me | Theorems.Thm_GlobalTheory_PairOp_adjointIdentities
-- name    : GlobalTheory.PairOp.adjointIdentities
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:43:50.936202+00:00
-- url     : https://prove2.me/theorems/c15dd6ee-1e10-4575-b059-d9d02051cf38
-- title:
--   Pair Op: adjoint Identities
-- statement:
--   The Pair Op construction uses the adjoint Identities property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/PairOperatorStatement.lean#L622-L685
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/PairOperatorStatement.lean#L622-L685

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

theorem GlobalTheory.PairOp.adjointIdentities [Fintype n] {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) :
    AdjointIdentities k n q (resChar ψ hψ q) := by sorry
