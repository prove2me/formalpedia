-- Prove2me | Theorems.Thm_GlobalTheory_T_norm_div_localEmbedding_close_to_one
-- name    : GlobalTheory.T.norm_div_localEmbedding_close_to_one
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:55:02.779024+00:00
-- url     : https://prove2.me/theorems/70ac054a-4b3f-4a46-b95d-0d183dcd98f5
-- title:
--   T: norm div local Embedding close to one
-- statement:
--   The T construction uses the norm div local Embedding close to one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormDivLocalEmbeddingCloseToOneStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormDivLocalEmbeddingCloseToOneStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormDivLocalEmbeddingCloseToOne
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NormCloseToOneOfCloseAbovePlace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormDivLocalEmbeddingCloseToOneStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.norm_div_localEmbedding_close_to_one : ∀ (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E'] (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) (w' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E')) (σ : E' →+* w.adicCompletion E), (∀ x : E, σ (algebraMap E E' x) = algebraMap E _ x) → (∀ x : E', Valued.v (σ x) = w'.valuation E' x) → ∀ M : ℕ, ∃ M' : ℕ, ∀ z : E', z ≠ 0 → (∀ w'' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E'), w''.asIdeal.comap (algebraMap (NumberField.RingOfIntegers E) (NumberField.RingOfIntegers E')) = w.asIdeal → w'' ≠ w' → w''.valuation E' (z - 1) ≤ WithZero.exp (-(M' : ℤ))) → Valued.v (algebraMap E (w.adicCompletion E) (Algebra.norm E z) / σ z - 1) ≤ WithZero.exp (-(M : ℤ)) := by sorry
