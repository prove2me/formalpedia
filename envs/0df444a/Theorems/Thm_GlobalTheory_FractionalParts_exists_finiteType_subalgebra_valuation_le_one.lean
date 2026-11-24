-- Prove2me | Theorems.Thm_GlobalTheory_FractionalParts_exists_finiteType_subalgebra_valuation_le_one
-- name    : GlobalTheory.FractionalParts.exists_finiteType_subalgebra_valuation_le_one
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T13:35:44.292601+00:00
-- url     : https://prove2.me/theorems/196b4ef3-3e01-49c0-9ea9-f6d173a40231
-- title:
--   Fractional Parts: exists finite Type subalgebra valuation le one
-- statement:
--   The Fractional Parts construction uses the exists finite Type subalgebra valuation le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsFiniteTypeSubalgebraValuationLeOne.lean#L18-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsFiniteTypeSubalgebraValuationLeOne.lean#L18-L69

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsFiniteTypeSubalgebraValuationLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FractionalParts

theorem GlobalTheory.FractionalParts.exists_finiteType_subalgebra_valuation_le_one (A B k : Type) [CommRing A] [CommRing B]
    [IsLocalRing B] [Algebra A B] [Algebra.EssFiniteType A B] [Field k] (φ : B →+* k)
    (V : ValuationSubring k) (hker : RingHom.ker φ = IsLocalRing.maximalIdeal B)
    (hA : ∀ a : A, V.valuation (φ (algebraMap A B a)) ≤ 1) :
    ∃ C : Subalgebra A B, Algebra.FiniteType A C ∧ (∀ c ∈ C, V.valuation (φ c) ≤ 1) ∧
      ∀ b : B, ∃ a ∈ C, ∃ s ∈ C, IsUnit s ∧ s * b = a := by sorry
