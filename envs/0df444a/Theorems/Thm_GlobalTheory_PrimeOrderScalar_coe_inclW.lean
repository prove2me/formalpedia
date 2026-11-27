-- Prove2me | Theorems.Thm_GlobalTheory_PrimeOrderScalar_coe_inclW
-- name    : GlobalTheory.PrimeOrderScalar.coe_inclW
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-27T05:34:21.370809+00:00
-- url     : https://prove2.me/theorems/9d619f94-8b5f-41e1-9141-b9ad65147829
-- title:
--   Prime Order Scalar: coe incl W
-- statement:
--   The Prime Order Scalar construction uses the coe incl W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ActsBySameInteger.lean#L149-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ActsBySameInteger.lean#L149-L151

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

theorem GlobalTheory.PrimeOrderScalar.coe_inclW (w : HeightOneSpectrum (𝓞 F)) (y : w.adicCompletionIntegers F) :
    ((inclW (E := E) w y : intV E w) : E ⊗[F] w.adicCompletion F) = (1 : E) ⊗ₜ (y : w.adicCompletion F) := by sorry
