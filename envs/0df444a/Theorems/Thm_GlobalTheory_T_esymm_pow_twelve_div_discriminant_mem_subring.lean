-- Prove2me | Theorems.Thm_GlobalTheory_T_esymm_pow_twelve_div_discriminant_mem_subring
-- name    : GlobalTheory.T.esymm_pow_twelve_div_discriminant_mem_subring
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:34:30.962548+00:00
-- url     : https://prove2.me/theorems/941ebf45-251b-41d0-b2f2-406d59316bf4
-- title:
--   T: esymm pow twelve div discriminant mem subring
-- statement:
--   The T construction uses the esymm pow twelve div discriminant mem subring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EsymmPowTwelveDivDiscriminantMemSubringStatement.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EsymmPowTwelveDivDiscriminantMemSubringStatement.lean#L11-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EsymmPowTwelveDivDiscriminantMemSubring
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModQPrin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModJTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EsymmPowTwelveDivDiscriminantMemSubringStatement
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
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.esymm_pow_twelve_div_discriminant_mem_subring : ∀ (ι : Type) [Fintype ι] (act : ι → SL(2, ℤ) → ι) (w N : ℕ) (f : ι → ℍ → ℂ) (R : Subring ℂ) (τ₀ : ℍ), 0 < N → ActBij act → IsFam act w f → (∀ i, QAll (· ∈ R) N (f i)) → jT τ₀ ∈ R → ∀ k : ℕ, (∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, f i τ₀ ^ 12 / DD τ₀ ^ w) ∈ R := by sorry
