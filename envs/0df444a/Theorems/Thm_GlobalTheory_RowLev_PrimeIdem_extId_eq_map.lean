-- Prove2me | Theorems.Thm_GlobalTheory_RowLev_PrimeIdem_extId_eq_map
-- name    : GlobalTheory.RowLev.PrimeIdem.extId_eq_map
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:32:20.671803+00:00
-- url     : https://prove2.me/theorems/8b128cc2-b5f3-40a3-8ad8-b4d7e3b6ce26
-- title:
--   Prime Idem: ext Id eq map
-- statement:
--   The Prime Idem construction uses the ext Id eq map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsPrimeIdempotentIntegralAdeles.lean#L238-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsPrimeIdempotentIntegralAdeles.lean#L238-L242

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

theorem GlobalTheory.RowLev.PrimeIdem.extId_eq_map (I : AutInst) (𝔞 : Ideal (𝓞 I.E)) : extId I 𝔞 = 𝔞.map (Inhab.psi I.F I.E) := by sorry
