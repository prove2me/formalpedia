-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_UnitFrame_normSq_eq_scalar_mul_form
-- name    : GlobalTheory.CompanionTheory.UnitFrame.normSq_eq_scalar_mul_form
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:19:48.28368+00:00
-- url     : https://prove2.me/theorems/400ad93a-e6d7-4fb3-97a8-d6a1ebc76b54
-- title:
--   Unit Frame: norm Sq eq scalar mul form
-- statement:
--   The Unit Frame construction uses the norm Sq eq scalar mul form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnitaryFramesPreserveNormSqSum.lean#L6-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnitaryFramesPreserveNormSqSum.lean#L6-L33

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnitaryFramesPreserveNormSqSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnitFrame

theorem GlobalTheory.CompanionTheory.UnitFrame.normSq_eq_scalar_mul_form {m : ℕ} (J : Matrix (Fin m) (Fin m) ℂ) (fr : GL (Fin m) ℂ)
    (ζ : ℂ) (s : ℤˣ)
    (h : ζ • (fr.1ᵀ * J * fr.1.map star) = ((s : ℤ) : ℂ) • 1) (v : Fin m → ℂ) :
    ((∑ a, ‖((fr⁻¹).1 *ᵥ v) a‖ ^ 2 : ℝ) : ℂ) =
      (((s : ℤ) : ℂ) * star ζ) * (star v ⬝ᵥ (J.map star *ᵥ v)) := by sorry
