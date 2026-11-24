-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_conj_places_transitive
-- name    : GlobalTheory.QNorm.conj_places_transitive
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:23:27.551273+00:00
-- url     : https://prove2.me/theorems/64314fb8-8686-4450-ad61-4df6dbc12a53
-- title:
--   QNorm: conj places transitive
-- statement:
--   The QNorm construction uses the conj places transitive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/WithZeroEqOfLeExpIff.lean#L107-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/WithZeroEqOfLeExpIff.lean#L107-L148

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_WithZeroEqOfLeExpIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm
open NumberField IsDedekindDomain
open scoped WithZero

theorem GlobalTheory.QNorm.conj_places_transitive : ∀ (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E), _root_.GlobalTheory.QNorm.IsQuad δ θ σ →
    (∀ w : HeightOneSpectrum (𝓞 E), ∃ w' : HeightOneSpectrum (𝓞 E),
      w'.under (𝓞 F) = w.under (𝓞 F) ∧ ∀ y : E, w'.valuation E y = w.valuation E (σ y)) ∧
    ∀ w w' : HeightOneSpectrum (𝓞 E), w'.under (𝓞 F) = w.under (𝓞 F) →
      w' = w ∨ ∀ y : E, w'.valuation E y = w.valuation E (σ y) := by sorry
