-- Prove2me | Theorems.Thm_GlobalTheory_QFam_transport_power_sums
-- name    : GlobalTheory.QFam.transport_power_sums
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:03:26.829798+00:00
-- url     : https://prove2.me/theorems/fe57fd59-8e1d-4608-b3ae-1160d0b2da8c
-- title:
--   QFam: transport power sums
-- statement:
--   The QFam construction uses the transport power sums property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TransportPowerSumsModularFamilies.lean#L25-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TransportPowerSumsModularFamilies.lean#L25-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModQPrin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModJTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSLTwoPermutedModularFamilyAlgebraClosureStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LevelOneModularFormValueGaloisTransportStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QExpansionsCoeffwiseConjugateRingClosureStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PermutedModularFamilySumEsymmSlashInvariantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TransportPowerSumsModularFamilies
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
open GlobalTheory GlobalTheory.QFam

theorem GlobalTheory.QFam.transport_power_sums : ∀ (g : ℂ ≃+* ℂ) (ι S : Type) [Fintype ι] [Fintype S] (act : ι → SL(2, ℤ) → ι) (N : ℕ) (m : S → ℕ) (f f' : S → ι → ℍ → ℂ) (τ₀ τ₁ : ℍ) (ω₀ ω₁ : ℂ), 0 < N → ActBij act → (∀ s, IsFam act (m s) (f s)) → (∀ s i, QConj g N (f s i) (f' s i)) → g (E₄ τ₀ / ω₀ ^ 4) = E₄ τ₁ / ω₁ ^ 4 → g (E₆ τ₀ / ω₀ ^ 6) = E₆ τ₁ / ω₁ ^ 6 → ∀ μ : S → ℕ, ∑ i, ∏ s, g (f s i τ₀ / ω₀ ^ m s) ^ μ s = ∑ i, ∏ s, (f' s i τ₁ / ω₁ ^ m s) ^ μ s := by sorry
