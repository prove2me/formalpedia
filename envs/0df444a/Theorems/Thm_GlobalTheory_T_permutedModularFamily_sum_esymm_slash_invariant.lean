-- Prove2me | Theorems.Thm_GlobalTheory_T_permutedModularFamily_sum_esymm_slash_invariant
-- name    : GlobalTheory.T.permutedModularFamily_sum_esymm_slash_invariant
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:35:11.31022+00:00
-- url     : https://prove2.me/theorems/3bf9e71d-c3eb-4c7e-8348-9be07036acae
-- title:
--   T: permuted Modular Family sum esymm slash invariant
-- statement:
--   The T construction uses the permuted Modular Family sum esymm slash invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PermutedModularFamilySumEsymmSlashInvariantStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PermutedModularFamilySumEsymmSlashInvariantStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PermutedModularFamilySumEsymmSlashInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PermutedModularFamilySumEsymmSlashInvariantStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.permutedModularFamily_sum_esymm_slash_invariant : ∀ (ι : Type) [Fintype ι] (act : ι → SL(2, ℤ) → ι) (w : ℤ) (f : ι → ℍ → ℂ), ActBij act → IsFam act w f → ∀ γ : SL(2, ℤ), ((fun τ => ∑ i, f i τ) ∣[w] γ = fun τ => ∑ i, f i τ) ∧ ∀ k : ℕ, ((fun τ => ∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, f i τ) ∣[(k * w : ℤ)] γ = fun τ => ∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, f i τ) := by sorry
