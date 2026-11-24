-- Prove2me | Theorems.Thm_GlobalTheory_T_torus_conjugation_preserves_congruence
-- name    : GlobalTheory.T.torus_conjugation_preserves_congruence
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:59:54.734545+00:00
-- url     : https://prove2.me/theorems/4a8c8a59-47d2-46fc-9527-c26e5b142fbf
-- title:
--   T: torus conjugation preserves congruence
-- statement:
--   The T construction uses the torus conjugation preserves congruence property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/TorusConjugationPreservesCongruenceStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/TorusConjugationPreservesCongruenceStatement.lean#L8-L9

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_TorusConjugationPreservesCongruence
import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsCongIdealTwoTorsion
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_TorusConjugationPreservesCongruenceStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.torus_conjugation_preserves_congruence : ∀ {L E ι : Type} [NormedField L] [Ring E] [Algebra L E] [Fintype ι] (wt : ι → ℕ) (P : ι → E), GlobalTheory.CompanionTheory.Iwahori.IsPieces P → ∀ J : AddSubgroup E, GlobalTheory.CompanionTheory.Iwahori.IsCongIdeal J P → (∀ c : L, ‖c‖ ≤ 1 → ∀ x ∈ J, c • x ∈ J) → ∀ (T T' : E) (τ : ι → L), (∀ i, τ i ≠ 0) → T * T' = 1 → T' * T = 1 → (∀ i, T * P i = τ i • P i) → (∀ i, P i * T = τ i • P i) → (∀ i j, wt i ≤ wt j → ‖τ i‖ ≤ ‖τ j‖) → ∀ a b : E, a - 1 ∈ J → b - 1 ∈ J → GlobalTheory.CompanionTheory.Iwahori.IsUpper wt P a → GlobalTheory.CompanionTheory.Iwahori.IsLower wt P b → T * a * T' - 1 ∈ J ∧ T' * b * T - 1 ∈ J := by sorry
