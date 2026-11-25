-- Prove2me | Theorems.Thm_GlobalTheory_exists_integral_dual_family
-- name    : GlobalTheory.exists_integral_dual_family
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:22:46.365877+00:00
-- url     : https://prove2.me/theorems/99e5e022-536c-4079-9ecc-bc9533e2774d
-- title:
--   Global Theory: exists integral dual family
-- statement:
--   The Global Theory construction uses the exists integral dual family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ComapSingleSpanAlgebraMapNumberField.lean#L7-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ComapSingleSpanAlgebraMapNumberField.lean#L7-L68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ComapSingleSpanAlgebraMapNumberField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Matrix
open scoped BigOperators
open GlobalTheory

theorem GlobalTheory.exists_integral_dual_family (E M : Type) [Field E] [NumberField E] [Field M]
    [NumberField M] [Algebra E M] :
    ∃ (k : ℕ) (b : Fin k → 𝓞 M) (l : Fin k → M →ₗ[E] E),
      (∀ j (c : 𝓞 M), ∃ a : 𝓞 E, l j (c : M) = (a : E)) ∧
      ∀ y : M, y = ∑ j, (b j : M) * algebraMap E M (l j y) := by sorry
