-- Prove2me | Theorems.Thm_GlobalTheory_RowLev_PrimeIdem_henselian_of_closure
-- name    : GlobalTheory.RowLev.PrimeIdem.henselian_of_closure
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:32:06.610798+00:00
-- url     : https://prove2.me/theorems/e2f65972-3116-42da-97a5-36bbcc5996ba
-- title:
--   Prime Idem: henselian of closure
-- statement:
--   The Prime Idem construction uses the henselian of closure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsPrimeIdempotentIntegralAdeles.lean#L16-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsPrimeIdempotentIntegralAdeles.lean#L16-L30

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

theorem GlobalTheory.RowLev.PrimeIdem.henselian_of_closure {O B S : Type} [CommRing O] [IsNoetherianRing O] [CommRing B] [Module.Finite ℤ B]
    [CommRing S] (t : O) [IsAdicComplete (Ideal.span {t}) O] (φ : O →+* S) (ψ : B →+* S)
    (h : ∀ T : Subring S, (∀ x, φ x ∈ T) → (∀ x, ψ x ∈ T) → ∀ x, x ∈ T) :
    HenselianRing S (Ideal.span {φ t}) := by sorry
