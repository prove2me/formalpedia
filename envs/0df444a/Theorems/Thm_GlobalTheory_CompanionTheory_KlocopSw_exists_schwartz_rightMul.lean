-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KlocopSw_exists_schwartz_rightMul
-- name    : GlobalTheory.CompanionTheory.KlocopSw.exists_schwartz_rightMul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:51:11.941183+00:00
-- url     : https://prove2.me/theorems/2e4a5cc7-c0fd-499f-9443-b51871c7c47e
-- title:
--   Klocop Sw: exists schwartz right Mul
-- statement:
--   The Klocop Sw construction uses the exists schwartz right Mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SchwartzLinearChange.lean#L27-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SchwartzLinearChange.lean#L27-L34

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SchwartzLinearChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix SchwartzMap
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KlocopSw

theorem GlobalTheory.CompanionTheory.KlocopSw.exists_schwartz_rightMul : ∀ (m n : ℕ) (c : ℂ) (a : Matrix (Fin n) (Fin n) ℂ), IsUnit a.det →
    ∀ φ : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ∃ ψ : SchwartzMap (Fin m → Fin n → ℂ) ℂ,
      ⇑ψ = fun u => c * φ (Matrix.of u * a) := by sorry
