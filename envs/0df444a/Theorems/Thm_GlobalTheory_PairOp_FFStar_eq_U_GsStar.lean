-- Prove2me | Theorems.Thm_GlobalTheory_PairOp_FFStar_eq_U_GsStar
-- name    : GlobalTheory.PairOp.FFStar_eq_U_GsStar
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:49.609564+00:00
-- url     : https://prove2.me/theorems/95ed62b6-942a-4e61-9c20-0f99a94880fd
-- title:
--   Pair Op: FFStar eq U Gs Star
-- statement:
--   The Pair Op construction uses the FFStar eq U Gs Star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/PairOperatorStatement.lean#L306-L350
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/PairOperatorStatement.lean#L306-L350

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
variable (χ)

theorem GlobalTheory.PairOp.FFStar_eq_U_GsStar {φ : Form k n M} (h : φ ∈ Mram k n M) : FFStar q χ φ = U q (GsStar χ φ) := by sorry
