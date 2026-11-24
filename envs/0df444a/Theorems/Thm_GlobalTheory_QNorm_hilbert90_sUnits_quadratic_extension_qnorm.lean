-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_hilbert90_sUnits_quadratic_extension_qnorm
-- name    : GlobalTheory.QNorm.hilbert90_sUnits_quadratic_extension_qnorm
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:02:42.206009+00:00
-- url     : https://prove2.me/theorems/f79ecfd9-2181-47b9-90b9-9181b64c47fd
-- title:
--   QNorm: hilbert90 s Units quadratic extension qnorm
-- statement:
--   The QNorm construction uses the hilbert90 s Units quadratic extension qnorm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/Hilbert90SUnitsQuadraticExtension.lean#L95-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/Hilbert90SUnitsQuadraticExtension.lean#L95-L158

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsQuadraticSqrtExtensionBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_WithZeroEqOfLeExpIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HeightOneSpectrumPlacesOverFiniteSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ValuationUnramifiedOfUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSupersetMemSUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitValuationEqOfAdm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_Hilbert90SUnitsQuadraticExtension
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

theorem GlobalTheory.QNorm.hilbert90_sUnits_quadratic_extension_qnorm : ∀ (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E), _root_.GlobalTheory.QNorm.IsQuad δ θ σ →
    ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (SE : Finset (HeightOneSpectrum (𝓞 E))),
    (∀ w : HeightOneSpectrum (𝓞 E), w ∈ SE ↔ w.under (𝓞 F) ∈ S) → _root_.GlobalTheory.QNorm.admitted F S →
    (∀ v, v ∉ S → v.valuation F δ = 1) → ∀ u : Eˣ, u ∈ _root_.GlobalTheory.QNorm.sUnits E SE →
    (u : E) * σ u = 1 → ∃ y : Eˣ, y ∈ _root_.GlobalTheory.QNorm.sUnits E SE ∧ (u : E) = y / σ y := by sorry
