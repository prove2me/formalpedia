-- Prove2me | Theorems.Thm_GlobalTheory_QFam_eis_q
-- name    : GlobalTheory.QFam.eis_q
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:59:43.82617+00:00
-- url     : https://prove2.me/theorems/459d7ca0-fa9e-4506-89f4-b75a2c1db18d
-- title:
--   QFam: eis q
-- statement:
--   The QFam construction uses the eis q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EisensteinDeltaQExpansionIntegrality.lean#L71-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EisensteinDeltaQExpansionIntegrality.lean#L71-L75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModQPrin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModJTau
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEvalMF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EisensteinDeltaQExpansionIntegrality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory GlobalTheory.QFam

theorem GlobalTheory.QFam.eis_q : ∀ (N : ℕ), 0 < N → ∀ F : ℍ → ℂ, (F = ⇑E₄ ∨ F = ⇑E₆ ∨ F = DD) →
    (∃ a : ℕ → ℤ, HasQ N F fun n => (a n : ℂ)) ∧ (∀ R : Subring ℂ, QAll (· ∈ R) N F) ∧
      ∀ g : ℂ ≃+* ℂ, QConj g N F F := by sorry
