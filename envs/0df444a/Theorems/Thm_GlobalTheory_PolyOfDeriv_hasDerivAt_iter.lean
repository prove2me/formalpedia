-- Prove2me | Theorems.Thm_GlobalTheory_PolyOfDeriv_hasDerivAt_iter
-- name    : GlobalTheory.PolyOfDeriv.hasDerivAt_iter
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:54:35.690448+00:00
-- url     : https://prove2.me/theorems/496d5d19-ba46-4c1a-a905-7cee8c062810
-- title:
--   Poly Of Deriv: has Deriv At iter
-- statement:
--   The Poly Of Deriv construction uses the has Deriv At iter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/EqEvalOfDirDerivVanish.lean#L46-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/EqEvalOfDirDerivVanish.lean#L46-L57

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

theorem GlobalTheory.PolyOfDeriv.hasDerivAt_iter {u : E → ℂ} (hu : ContDiff ℝ ∞ u) (k : ℕ) (y x : E) (t : ℝ) :
    HasDerivAt (fun t : ℝ => iteratedFDeriv ℝ k u (y + t • x) (fun _ => x))
      (iteratedFDeriv ℝ (k+1) u (y + t • x) (fun _ => x)) t := by sorry
