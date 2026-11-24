-- Prove2me | Theorems.Thm_GlobalTheory_QFam_transport_of_separating
-- name    : GlobalTheory.QFam.transport_of_separating
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:00:34.134107+00:00
-- url     : https://prove2.me/theorems/812a73f3-5de0-4358-8510-97c241e427f1
-- title:
--   QFam: transport of separating
-- statement:
--   The QFam construction uses the transport of separating property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TransportOfSeparating.lean#L13-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TransportOfSeparating.lean#L13-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModQPrin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModJTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPermTransportModularFamiliesValuesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TransportOfSeparating
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

theorem GlobalTheory.QFam.transport_of_separating : ∀ (g : ℂ ≃+* ℂ) (ι S : Type) [Fintype ι] [Fintype S] (act : ι → SL(2, ℤ) → ι) (N w : ℕ) (m : S → ℕ) (f f' : ι → ℍ → ℂ) (u u' : S → ι → ℍ → ℂ) (τ₀ τ₁ : ℍ) (ω₀ ω₁ : ℂ), 0 < N → ActBij act → IsFam act w f → (∀ s, IsFam act (m s) (u s)) → (∀ i, QConj g N (f i) (f' i)) → (∀ s i, QConj g N (u s i) (u' s i)) → ω₀ ≠ 0 → g (E₄ τ₀ / ω₀ ^ 4) = E₄ τ₁ / ω₁ ^ 4 → g (E₆ τ₀ / ω₀ ^ 6) = E₆ τ₁ / ω₁ ^ 6 → ∀ i i' : ι, (∀ j, (∀ s, u s j τ₀ = u s i τ₀) → f j τ₀ = f i τ₀) → (∀ s, g (u s i τ₀ / ω₀ ^ m s) = u' s i' τ₁ / ω₁ ^ m s) → g (f i τ₀ / ω₀ ^ w) = f' i' τ₁ / ω₁ ^ w := by sorry
