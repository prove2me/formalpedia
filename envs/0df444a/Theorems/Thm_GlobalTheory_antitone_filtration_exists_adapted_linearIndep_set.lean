-- Prove2me | Theorems.Thm_GlobalTheory_antitone_filtration_exists_adapted_linearIndep_set
-- name    : GlobalTheory.antitone_filtration_exists_adapted_linearIndep_set
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:05:55.681133+00:00
-- url     : https://prove2.me/theorems/368d2690-f4ca-4684-85b7-1a7ce29bac2e
-- title:
--   Global Theory: antitone filtration exists adapted linear Indep set
-- statement:
--   The Global Theory construction uses the antitone filtration exists adapted linear Indep set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AntitoneFiltrationExistsAdaptedLinearIndepSet.lean#L7-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AntitoneFiltrationExistsAdaptedLinearIndepSet.lean#L7-L57

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

theorem GlobalTheory.antitone_filtration_exists_adapted_linearIndep_set {L M : Type} [Field L] [AddCommGroup M] [Module L M]
    (A : ℤ → Submodule L M) (hA : Antitone A) (hi : ℤ) (hhi : A hi = ⊥) (n : ℕ) :
    ∃ (s : Set M) (k : M → ℤ), LinearIndepOn L id s ∧ (∀ x ∈ s, hi - n ≤ k x) ∧
      ∀ a, hi - n ≤ a → A a = span L {x | x ∈ s ∧ a ≤ k x} := by sorry
