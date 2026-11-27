-- Prove2me | Theorems.Thm_GlobalTheory_PrimeOrderScalar_inclW_algebraMap
-- name    : GlobalTheory.PrimeOrderScalar.inclW_algebraMap
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-27T05:31:21.458201+00:00
-- url     : https://prove2.me/theorems/3542066a-e3c4-4aa4-94cb-4a894278bc06
-- title:
--   Prime Order Scalar: incl W algebra Map
-- statement:
--   The Prime Order Scalar construction uses the incl W algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ActsBySameInteger.lean#L157-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ActsBySameInteger.lean#L157-L161

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

theorem GlobalTheory.PrimeOrderScalar.inclW_algebraMap (w : HeightOneSpectrum (𝓞 F)) (d : 𝓞 F) :
    ((inclW (E := E) w (algebraMap (𝓞 F) (w.adicCompletionIntegers F) d) : intV E w) :
      E ⊗[F] w.adicCompletion F) = algebraMap F E (d : F) ⊗ₜ (1 : w.adicCompletion F) := by sorry
