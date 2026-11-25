-- Prove2me | Theorems.Thm_GlobalTheory_PolyOfDeriv_eq_eval_of_dirDeriv_vanish
-- name    : GlobalTheory.PolyOfDeriv.eq_eval_of_dirDeriv_vanish
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:15:17.965225+00:00
-- url     : https://prove2.me/theorems/e60bcbe0-00e2-516f-b28d-2985a78e3399
-- title:
--   Poly Of Deriv: eq eval of dir Deriv vanish
-- statement:
--   The Poly Of Deriv construction uses the eq eval of dir Deriv vanish property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/EqEvalOfDirDerivVanish.lean#L86-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/EqEvalOfDirDerivVanish.lean#L86-L103

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

theorem GlobalTheory.PolyOfDeriv.eq_eval_of_dirDeriv_vanish : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ)
    (u : (ι → ℝ) → ℂ), ContDiff ℝ ∞ u →
    (∀ L : List (ι → ℝ), L.length = N →
      L.foldr (fun y g => fun x => deriv (fun t : ℝ => g (x + t • y)) 0) u = 0) →
    ∃ p : MvPolynomial ι ℂ, ∀ x, u x = MvPolynomial.eval (fun i => (x i : ℂ)) p := by sorry
