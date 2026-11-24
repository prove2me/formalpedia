-- Prove2me | Theorems.Thm_GlobalTheory_LocalDifferentProduct_prod_normDifferentV
-- name    : GlobalTheory.LocalDifferentProduct.prod_normDifferentV
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:45:48.720574+00:00
-- url     : https://prove2.me/theorems/8411d6f6-7528-4d55-aa29-89be1e83f8e9
-- title:
--   Local Different Product: prod norm Different V
-- statement:
--   The Local Different Product construction uses the prod norm Different V property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/FinprodLocalDifferentIdealNormEqDiscr.lean#L287-L385
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/FinprodLocalDifferentIdealNormEqDiscr.lean#L287-L385

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_LocalDualIndex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_HermitianFormFiniteZerosOnLineCmExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FinprodLocalDifferentIdealNormEqDiscr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Polynomial
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex
open GlobalTheory GlobalTheory.LocalDifferentProduct
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Polynomial

theorem GlobalTheory.LocalDifferentProduct.prod_normDifferentV : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [StarRing E] (σ : E →ₐ[F] E), _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → (∀ x : E, star x = σ x) →
    _root_.Formalism.HermitianLatticesTheory.IsCMUnram E → (Function.mulSupport (_root_.GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.normDifferentV F)).Finite ∧
      ((∏ᶠ v, _root_.GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.normDifferentV F v : ℕ) : ℝ) = _root_.GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.absDiscr F ∧
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.absDiscr F = (2 * _root_.Formalism.HermitianLatticesTheory.vInv E) ^ _root_.Formalism.HermitianLatticesTheory.fDeg E := by sorry
