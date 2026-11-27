-- Prove2me | Theorems.Thm_GlobalTheory_PrimeOrderScalar_coe_inclO
-- name    : GlobalTheory.PrimeOrderScalar.coe_inclO
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-27T05:30:11.365964+00:00
-- url     : https://prove2.me/theorems/e2e53a5b-f996-56a7-962c-c8712ba8b2d6
-- title:
--   Prime Order Scalar: coe incl O
-- statement:
--   The Prime Order Scalar construction uses the coe incl O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ActsBySameInteger.lean#L153-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ActsBySameInteger.lean#L153-L155

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

theorem GlobalTheory.PrimeOrderScalar.coe_inclO (w : HeightOneSpectrum (𝓞 F)) (o : 𝓞 E) :
    ((inclO w o : intV E w) : E ⊗[F] w.adicCompletion F) = (o : E) ⊗ₜ (1 : w.adicCompletion F) := by sorry
