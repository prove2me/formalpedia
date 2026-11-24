-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_perm_representatives_mod_similitude
-- name    : GlobalTheory.T.exists_perm_representatives_mod_similitude
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:36:46.534806+00:00
-- url     : https://prove2.me/theorems/ddf25038-d6da-471c-95fa-5d9d6560d3c5
-- title:
--   T: exists perm representatives mod similitude
-- statement:
--   The T construction uses the exists perm representatives mod similitude property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsRepresentativesModSimilitudeTransposeStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsRepresentativesModSimilitudeTransposeStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsRepresentativesModSimilitudeTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsRepresentativesModSimilitudeTransposeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_perm_representatives_mod_similitude : ∀ (g m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ), 1 ≤ m → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → ∃ k n : (Fin 4 → Fin (m ^ g)) → Fin 4 → Fin g → ℤ, ∀ k' n' : (Fin 4 → Fin (m ^ g)) → Fin 4 → Fin g → ℤ, (∀ I I', I ≠ I' → ¬ ∃ d e : Fin 4 → Fin g → ℤ, ∀ c, k' I c = k' I' c + ∑ r, al r c • d r ∧ n' I c = n' I' c + ∑ r, al r c • e r) → ∃ σ : Equiv.Perm (Fin 4 → Fin (m ^ g)), ∀ I, ∃ d e : Fin 4 → Fin g → ℤ, ∀ c, k' I c = k (σ I) c + ∑ r, al r c • d r ∧ n' I c = n (σ I) c + ∑ r, al r c • e r := by sorry
