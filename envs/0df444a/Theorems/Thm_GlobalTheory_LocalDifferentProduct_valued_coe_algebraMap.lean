-- Prove2me | Theorems.Thm_GlobalTheory_LocalDifferentProduct_valued_coe_algebraMap
-- name    : GlobalTheory.LocalDifferentProduct.valued_coe_algebraMap
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:11:30.77515+00:00
-- url     : https://prove2.me/theorems/d69a9b87-91b3-4534-b5b5-01e3e62b3ef5
-- title:
--   Local Different Product: valued coe algebra Map
-- statement:
--   The Local Different Product construction uses the valued coe algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/FinprodLocalDifferentIdealNormEqDiscr.lean#L17-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/FinprodLocalDifferentIdealNormEqDiscr.lean#L17-L20

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

theorem GlobalTheory.LocalDifferentProduct.valued_coe_algebraMap (x : 𝓞 K) :
    Valued.v ((algebraMap (𝓞 K) (v.adicCompletionIntegers K) x : v.adicCompletionIntegers K) :
      v.adicCompletion K) = v.intValuation x := by sorry
