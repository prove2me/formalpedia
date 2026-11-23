-- Prove2me | Theorems.Thm_GlobalTheory_Capelli_commute_colOp_colOp
-- name    : GlobalTheory.Capelli.commute_colOp_colOp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:50:07.588483+00:00
-- url     : https://prove2.me/theorems/39090e9a-3459-4645-abe3-f63345abfb18
-- title:
--   Capelli: commute col Op col Op
-- statement:
--   The Capelli construction uses the commute col Op col Op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CommuteRowOpRightMixedOp.lean#L102-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CommuteRowOpRightMixedOp.lean#L102-L106

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

theorem GlobalTheory.Capelli.commute_colOp_colOp [Fintype I] [Fintype I'] (z : I × J → σ) (y : I' × J' → σ)
    (hzy : ∀ u w, z u ≠ y w) (i j : J) (k l : J') :
    Commute (colOp K z i j) (colOp K y k l) := by sorry
