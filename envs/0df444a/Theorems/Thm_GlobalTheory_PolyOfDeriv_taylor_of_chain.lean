-- Prove2me | Theorems.Thm_GlobalTheory_PolyOfDeriv_taylor_of_chain
-- name    : GlobalTheory.PolyOfDeriv.taylor_of_chain
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:50:09.619845+00:00
-- url     : https://prove2.me/theorems/b04e7aeb-d984-4a99-830f-34944f62206e
-- title:
--   Poly Of Deriv: taylor of chain
-- statement:
--   The Poly Of Deriv construction uses the taylor of chain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/EqEvalOfDirDerivVanish.lean#L6-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/EqEvalOfDirDerivVanish.lean#L6-L42

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

theorem GlobalTheory.PolyOfDeriv.taylor_of_chain (N : ℕ) : ∀ (G : ℕ → ℝ → ℂ) (_ : ∀ k t, HasDerivAt (G k) (G (k+1) t) t)
    (_ : G N = 0) (t : ℝ),
    G 0 t = ∑ k ∈ Finset.range N, G k 0 * ((t ^ k / k.factorial : ℝ) : ℂ) := by sorry
