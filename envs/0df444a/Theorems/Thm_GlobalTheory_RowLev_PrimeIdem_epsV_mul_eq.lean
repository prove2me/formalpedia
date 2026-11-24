-- Prove2me | Theorems.Thm_GlobalTheory_RowLev_PrimeIdem_epsV_mul_eq
-- name    : GlobalTheory.RowLev.PrimeIdem.epsV_mul_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:27:12.598511+00:00
-- url     : https://prove2.me/theorems/8fdfe661-035b-4a67-936a-5ba891a64c32
-- title:
--   Prime Idem: eps V mul eq
-- statement:
--   The Prime Idem construction uses the eps V mul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsPrimeIdempotentIntegralAdeles.lean#L165-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsPrimeIdempotentIntegralAdeles.lean#L165-L170

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsDual
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsAdicCompleteAndCardQuotientAdicCompletionInteg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsPrimeIdempotentIntegralAdeles
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical
open GlobalTheory GlobalTheory.RowLev
open GlobalTheory.RowLev.PrimeIdem
open Formalism.UG Formalism.UG.P
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem GlobalTheory.RowLev.PrimeIdem.epsV_mul_eq (v : HeightOneSpectrum (𝓞 F)) {x y : IntAf F E} (h : prInt E v x = prInt E v y) :
    epsV E v * x = epsV E v * y := by sorry
