-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_exists_norm_uniformizer_of_split
-- name    : GlobalTheory.QNorm.exists_norm_uniformizer_of_split
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:02:34.816187+00:00
-- url     : https://prove2.me/theorems/eda31e52-f155-4483-b873-20f2ea097355
-- title:
--   QNorm: exists norm uniformizer of split
-- statement:
--   The QNorm construction uses the exists norm uniformizer of split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsAdmissibleLocalNormMemSUnitsSupGlobalNorm.lean#L51-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsAdmissibleLocalNormMemSUnitsSupGlobalNorm.lean#L51-L86

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_EvenNormsOfUnitNonsquare
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsAdmissibleSupersetFinitePlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSupersetMemSUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsQuadraticSqrtExtensionOfNotSquare
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsQuadraticSqrtExtensionBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HeightOneSpectrumPlacesOverFiniteSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_WithZeroEqOfLeExpIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ValuationUnramifiedOfUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsTwoPlacesOverOfIsSquareLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsAdmissibleLocalNormMemSUnitsSupGlobalNorm
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

theorem GlobalTheory.QNorm.exists_norm_uniformizer_of_split {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] {δ : F} {θ : E} {σ : E ≃ₐ[F] E} (hq : IsQuad δ θ σ)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (SE : Finset (HeightOneSpectrum (𝓞 E)))
    (hS : admitted F S) (hSE : admitted E SE) (hover : ∀ w, w ∈ SE ↔ w.under (𝓞 F) ∈ S)
    (hδ : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → v.valuation F δ = 1)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S)
    (hsq : IsSquare (algebraMap F (v.adicCompletion F) δ)) :
    ∃ a b : F, v.valuation F (a ^ 2 - δ * b ^ 2) = WithZero.exp (-1) ∧
      ∀ u : HeightOneSpectrum (𝓞 F), u ∉ S → u ≠ v → u.valuation F (a ^ 2 - δ * b ^ 2) = 1 := by sorry
