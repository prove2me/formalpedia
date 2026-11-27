-- Prove2me | Theorems.Thm_GlobalTheory_PrimeOrderScalar_isUnit_algebraMap
-- name    : GlobalTheory.PrimeOrderScalar.isUnit_algebraMap
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-27T05:31:36.074876+00:00
-- url     : https://prove2.me/theorems/23c5a202-6605-4de7-88e4-0edc1b9cf41d
-- title:
--   Prime Order Scalar: is Unit algebra Map
-- statement:
--   The Prime Order Scalar construction uses the is Unit algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ActsBySameInteger.lean#L163-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ActsBySameInteger.lean#L163-L169

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ActsBySameInteger
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Matrix
open GlobalTheory GlobalTheory.PrimeOrderScalar
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem GlobalTheory.PrimeOrderScalar.isUnit_algebraMap (w : HeightOneSpectrum (𝓞 F)) (d : 𝓞 F) (hd : d ∉ w.asIdeal) :
    IsUnit (algebraMap (𝓞 F) (w.adicCompletionIntegers F) d) := by sorry
