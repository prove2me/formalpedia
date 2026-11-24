-- Prove2me | Theorems.Thm_GlobalTheory_RowLev_PrimeIdem_mem_map_of_apply_eq_zero
-- name    : GlobalTheory.RowLev.PrimeIdem.mem_map_of_apply_eq_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:27:17.782713+00:00
-- url     : https://prove2.me/theorems/0b9dbee6-9cc0-460c-92cf-ab67181f829d
-- title:
--   Prime Idem: mem map of apply eq zero
-- statement:
--   The Prime Idem construction uses the mem map of apply eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsPrimeIdempotentIntegralAdeles.lean#L201-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsPrimeIdempotentIntegralAdeles.lean#L201-L223

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

theorem GlobalTheory.RowLev.PrimeIdem.mem_map_of_apply_eq_zero (u : HeightOneSpectrum (𝓞 E)) (y : Af F) (hy : y ∈ intAd F)
    (h0 : y (u.under (𝓞 F)) = 0) (z : IntAf F E) (hz : z.1 = (1 : E) ⊗ₜ[F] y) :
    z ∈ u.asIdeal.map (Inhab.psi F E) := by sorry
