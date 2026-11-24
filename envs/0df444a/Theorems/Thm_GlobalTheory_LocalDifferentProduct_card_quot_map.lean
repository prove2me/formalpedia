-- Prove2me | Theorems.Thm_GlobalTheory_LocalDifferentProduct_card_quot_map
-- name    : GlobalTheory.LocalDifferentProduct.card_quot_map
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:14:18.705687+00:00
-- url     : https://prove2.me/theorems/4aaf51b9-c06f-4746-8db9-b89db7b4fd5e
-- title:
--   Local Different Product: card quot map
-- statement:
--   The Local Different Product construction uses the card quot map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/FinprodLocalDifferentIdealNormEqDiscr.lean#L219-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/FinprodLocalDifferentIdealNormEqDiscr.lean#L219-L256

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
variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Polynomial
variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem GlobalTheory.LocalDifferentProduct.card_quot_map {I : Ideal (𝓞 K)} (hI : I ≠ 0) :
    Nat.card (v.adicCompletionIntegers K ⧸
      I.map (algebraMap (𝓞 K) (v.adicCompletionIntegers K))) =
      Ideal.absNorm (v.maxPowDividing I) := by sorry
