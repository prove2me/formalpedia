-- Prove2me | Theorems.Thm_GlobalTheory_CoprimeBasis_exists_coprime_basis
-- name    : GlobalTheory.CoprimeBasis.exists_coprime_basis
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:27:19.229654+00:00
-- url     : https://prove2.me/theorems/737413b1-379a-4238-8809-d167acc58a28
-- title:
--   Coprime Basis: exists coprime basis
-- statement:
--   The Coprime Basis construction uses the exists coprime basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIndependentBasisCoprime.lean#L28-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIndependentBasisCoprime.lean#L28-L117

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemLocDIffSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIndependentBasisCoprime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.CoprimeBasis

theorem GlobalTheory.CoprimeBasis.exists_coprime_basis : ∀ (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] [Module.Finite ℤ M] [IsAddTorsionFree M] (N : ℕ), 2 ≤ N → ∃ (r : ℕ) (x : Fin r → M), LinearIndependent (𝓞 F) x ∧ ∃ c : 𝓞 F, c ≠ 0 ∧ IsCoprime c (N : 𝓞 F) ∧ ∀ m : M, c • m ∈ Submodule.span (𝓞 F) (Set.range x) := by sorry
