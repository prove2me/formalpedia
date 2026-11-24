-- Prove2me | Theorems.Thm_GlobalTheory_exists_isHomogeneous_dehomogenize
-- name    : GlobalTheory.exists_isHomogeneous_dehomogenize
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:33:01.163698+00:00
-- url     : https://prove2.me/theorems/2a7d9b2b-9381-48cf-aa94-12caad8d4613
-- title:
--   Global Theory: exists is Homogeneous dehomogenize
-- statement:
--   The Global Theory construction uses the exists is Homogeneous dehomogenize property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIsHomogeneousDehomogenize.lean#L6-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIsHomogeneousDehomogenize.lean#L6-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIsHomogeneousDehomogenize
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory

theorem GlobalTheory.exists_isHomogeneous_dehomogenize : ∀ {D : ℕ} (T₀ : MvPolynomial (Fin D) ℤ) (q : ℕ),
    T₀.totalDegree ≤ q → ∃ T : MvPolynomial (Fin (D + 1)) ℤ, T.IsHomogeneous q ∧
      ∀ (R : Type) [CommRing R] (a : Fin (D + 1) → R), a 0 = 1 →
        aeval a T = aeval (fun j => a j.succ) T₀ := by sorry
