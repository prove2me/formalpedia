-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_first_inequality_sUnits
-- name    : GlobalTheory.QNorm.first_inequality_sUnits
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:09.8248+00:00
-- url     : https://prove2.me/theorems/f0e6b5da-cc1e-4953-9285-bce1636c8be6
-- title:
--   QNorm: first inequality s Units
-- statement:
--   The QNorm construction uses the first inequality s Units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/FirstInequalitySUnits.lean#L61-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/FirstInequalitySUnits.lean#L61-L147

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexFormulaNormsInvolutionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsQuadraticSqrtExtensionBasicFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TwoMulCardPlacesLeCardOverQuadraticStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TwoMulCardInfinitePlaceLeQuadraticStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsQuadraticSqrtExtensionOfNotSquareStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SUnitsPlacesOverAndQuadraticConjStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_Hilbert90SUnitsQuadraticExtensionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HeightOneSpectrumPlacesOverFiniteSetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_RelIndexSquaresSUnitsNumberFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FirstInequalitySUnits
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

theorem GlobalTheory.QNorm.first_inequality_sUnits :
    ∀ (F : Type) [Field F] [NumberField F] (δ : Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))),
      admitted F S → δ ∈ sUnits F S → ¬ IsSquare (δ : F) →
      (normSub (RingHom.id F) (δ : F)).relIndex (sUnits F S) ≠ 0 ∧
        2 * (normSub (RingHom.id F) (δ : F)).relIndex (sUnits F S) ≤
          2 ^ (tFin F δ S + tReal F δ) := by sorry
