-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_mem_sUnits_sup_of_local_orders
-- name    : GlobalTheory.QNorm.mem_sUnits_sup_of_local_orders
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:02:35.977199+00:00
-- url     : https://prove2.me/theorems/e12160b4-4bd7-4ecb-bef0-952320a0796f
-- title:
--   QNorm: mem s Units sup of local orders
-- statement:
--   The QNorm construction uses the mem s Units sup of local orders property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsAdmissibleLocalNormMemSUnitsSupGlobalNorm.lean#L17-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsAdmissibleLocalNormMemSUnitsSupGlobalNorm.lean#L17-L49

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

theorem GlobalTheory.QNorm.mem_sUnits_sup_of_local_orders {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (N : Subgroup Fˣ) (t : Fˣ)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → ∃ n ∈ N,
      v.valuation F (n : F) = v.valuation F (t : F) ∧
      ∀ w : HeightOneSpectrum (𝓞 F), w ∉ S → w ≠ v → w.valuation F (n : F) = 1) :
    t ∈ sUnits F S ⊔ N := by sorry
