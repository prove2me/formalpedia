-- Prove2me | Theorems.Thm_GlobalTheory_Capelli_commute_rowOp_colOp
-- name    : GlobalTheory.Capelli.commute_rowOp_colOp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:50:19.310797+00:00
-- url     : https://prove2.me/theorems/89a19e83-4c0e-43c7-acaa-9296d3e2f493
-- title:
--   Capelli: commute row Op col Op
-- statement:
--   The Capelli construction uses the commute row Op col Op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CommuteRowOpRightMixedOp.lean#L114-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CommuteRowOpRightMixedOp.lean#L114-L118

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CommuteRowOpRightMixedOp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.Capelli
variable {K σ : Type*} [CommRing K]
variable {I J I' J' : Type*}

theorem GlobalTheory.Capelli.commute_rowOp_colOp [Fintype J] [Fintype I'] (z : I × J → σ) (y : I' × J' → σ)
    (hzy : ∀ u w, z u ≠ y w) (a b : I) (k l : J') :
    Commute (rowOp K z a b) (colOp K y k l) := by sorry
