-- Prove2me | Theorems.Thm_GlobalTheory_filtration_adapted_basis
-- name    : GlobalTheory.filtration_adapted_basis
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T09:52:27.029175+00:00
-- url     : https://prove2.me/theorems/d8e6df5e-8313-408e-82c3-130d7674ad1f
-- title:
--   Global Theory: filtration adapted basis
-- statement:
--   The Global Theory construction uses the filtration adapted basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AntitoneFiltrationExistsAdaptedLinearIndepSet.lean#L59-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AntitoneFiltrationExistsAdaptedLinearIndepSet.lean#L59-L138

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AntitoneFiltrationExistsAdaptedLinearIndepSet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Submodule

theorem GlobalTheory.filtration_adapted_basis {L M : Type} [Field L] [AddCommGroup M] [Module L M]
    (A : ℤ → Submodule L M) (hA : Antitone A) (hfd : FiniteDimensional L ↥(⨆ a, A a))
    (hsep : ∀ x, (∀ a, x ∈ A a) → x = 0) :
    ∃ (m : ℕ) (d : Fin m → M) (k : Fin m → ℤ), LinearIndependent L d ∧
      ∀ a, A a = Submodule.span L (d '' {i | a ≤ k i}) := by sorry
