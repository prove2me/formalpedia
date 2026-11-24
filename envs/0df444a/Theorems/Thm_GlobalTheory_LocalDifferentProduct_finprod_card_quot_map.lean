-- Prove2me | Theorems.Thm_GlobalTheory_LocalDifferentProduct_finprod_card_quot_map
-- name    : GlobalTheory.LocalDifferentProduct.finprod_card_quot_map
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:14:01.666433+00:00
-- url     : https://prove2.me/theorems/804c5d7e-e2b7-48c7-adf6-90c6dbae30d3
-- title:
--   Local Different Product: finprod card quot map
-- statement:
--   The Local Different Product construction uses the finprod card quot map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/FinprodLocalDifferentIdealNormEqDiscr.lean#L262-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/FinprodLocalDifferentIdealNormEqDiscr.lean#L262-L276

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

theorem GlobalTheory.LocalDifferentProduct.finprod_card_quot_map {K : Type} [Field K] [NumberField K] {I : Ideal (𝓞 K)} (hI : I ≠ 0) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) => Nat.card (v.adicCompletionIntegers K ⧸
      I.map (algebraMap (𝓞 K) (v.adicCompletionIntegers K)))).Finite ∧
    ∏ᶠ v : HeightOneSpectrum (𝓞 K), Nat.card (v.adicCompletionIntegers K ⧸
      I.map (algebraMap (𝓞 K) (v.adicCompletionIntegers K))) = Ideal.absNorm I := by sorry
