-- Prove2me | Theorems.Thm_GlobalTheory_PairOp_smul_up
-- name    : GlobalTheory.PairOp.smul_up
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:41:41.508801+00:00
-- url     : https://prove2.me/theorems/c81f5908-3797-4ad1-bbba-2f49d7748b79
-- title:
--   Pair Op: smul up
-- statement:
--   The Pair Op construction uses the smul up property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/PairOperatorStatement.lean#L18-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/PairOperatorStatement.lean#L18-L30

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

theorem GlobalTheory.PairOp.smul_up (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] (q : Unif k) (c : 𝓀[k]ˣ) (x : {x : Red L // x ≠ 0}) :
    c • up L q x = up L q ⟨((c⁻¹ : 𝓀[k]ˣ) : 𝓀[k]) • x.1, smul_ne_zero (c⁻¹).ne_zero x.2⟩ := by sorry
