-- Prove2me | Theorems.Thm_GlobalTheory_PairOp_FF_FFStar_ram
-- name    : GlobalTheory.PairOp.FF_FFStar_ram
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:41:07.668344+00:00
-- url     : https://prove2.me/theorems/48807f64-75be-4fad-9ede-4650c06c4497
-- title:
--   Pair Op: FF FFStar ram
-- statement:
--   The Pair Op construction uses the FF FFStar ram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/PairOperatorStatement.lean#L360-L362
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/PairOperatorStatement.lean#L360-L362

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

theorem GlobalTheory.PairOp.FF_FFStar_ram [Fintype n] (hχ : χ ≠ 1) {φ : Form k n M} (h : φ ∈ Mram k n M) :
    FF q χ (FFStar q χ φ) = ((resCard k : ℂ) ^ Fintype.card n) • φ := by sorry
