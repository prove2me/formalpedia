-- Prove2me | Theorems.Thm_GlobalTheory_Capelli_commute_rowOp_colOp_self
-- name    : GlobalTheory.Capelli.commute_rowOp_colOp_self
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:49:58.540161+00:00
-- url     : https://prove2.me/theorems/c04b558e-a3a2-41a6-ad35-df533403a55d
-- title:
--   Capelli: commute row Op col Op self
-- statement:
--   The Capelli construction uses the commute row Op col Op self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CommuteRowOpRightMixedOp.lean#L120-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CommuteRowOpRightMixedOp.lean#L120-L131

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

theorem GlobalTheory.Capelli.commute_rowOp_colOp_self [Fintype I] [Fintype J] (z : I × J → σ)
    (hz : Function.Injective z) (a b : I) (k l : J) :
    Commute (rowOp K z a b) (colOp K z k l) := by sorry
