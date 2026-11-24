-- Prove2me | Theorems.Thm_GlobalTheory_PolyOfDeriv_foldr_replicate
-- name    : GlobalTheory.PolyOfDeriv.foldr_replicate
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:50:22.6111+00:00
-- url     : https://prove2.me/theorems/5e7dc62c-df51-40fc-b5ca-ad005b268cdb
-- title:
--   Poly Of Deriv: foldr replicate
-- statement:
--   The Poly Of Deriv construction uses the foldr replicate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/EqEvalOfDirDerivVanish.lean#L59-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/EqEvalOfDirDerivVanish.lean#L59-L69

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_EqEvalOfDirDerivVanish
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open GlobalTheory GlobalTheory.PolyOfDeriv
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem GlobalTheory.PolyOfDeriv.foldr_replicate {u : E → ℂ} (hu : ContDiff ℝ ∞ u) (x : E) (k : ℕ) :
    (List.replicate k x).foldr
      (fun y g => fun z => deriv (fun t : ℝ => g (z + t • y)) 0) u
      = fun y => iteratedFDeriv ℝ k u y (fun _ => x) := by sorry
