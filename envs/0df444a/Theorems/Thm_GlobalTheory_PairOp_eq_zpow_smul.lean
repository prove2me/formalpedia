-- Prove2me | Theorems.Thm_GlobalTheory_PairOp_eq_zpow_smul
-- name    : GlobalTheory.PairOp.eq_zpow_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:29:43.484407+00:00
-- url     : https://prove2.me/theorems/c022c584-6616-4530-915d-58595c31cf4e
-- title:
--   Pair Op: eq zpow smul
-- statement:
--   The Pair Op construction uses the eq zpow smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/PairOperatorStatement.lean#L364-L369
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/PairOperatorStatement.lean#L364-L369

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

theorem GlobalTheory.PairOp.eq_zpow_smul {φ φ' : Form k n M} {r : ℕ} (h : (resCard k : ℂ) • φ' = ((resCard k : ℂ) ^ r) • φ) :
    φ' = ((resCard k : ℂ) ^ ((r : ℤ) - 1)) • φ := by sorry
