-- Prove2me | Theorems.Thm_GlobalTheory_UnRep_NormOne_exists_split
-- name    : GlobalTheory.UnRep.NormOne.exists_split
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:23:14.121666+00:00
-- url     : https://prove2.me/theorems/87aa3b8c-cbe9-4903-b2df-ad81160a1242
-- title:
--   Norm One: exists split
-- statement:
--   The Norm One construction uses the exists split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/NormOneApproximationAtLevelPrimes.lean#L11-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/NormOneApproximationAtLevelPrimes.lean#L11-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ValuationEqOneOfNormOneOfNotMoved
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsDenominatorPrimesPrescribed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_NormOneApproximationAtLevelPrimes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.NormOne

theorem GlobalTheory.UnRep.NormOne.exists_split (N : ℕ) : ∀ M : ℕ, 0 < M → ∃ D₁ D₂ k : ℕ, M = D₁ * D₂ ∧ D₁ ∣ N ^ k ∧ D₂.Coprime N := by sorry
