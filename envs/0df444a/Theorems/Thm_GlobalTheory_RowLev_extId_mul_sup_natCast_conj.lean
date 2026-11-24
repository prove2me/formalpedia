-- Prove2me | Theorems.Thm_GlobalTheory_RowLev_extId_mul_sup_natCast_conj
-- name    : GlobalTheory.RowLev.extId_mul_sup_natCast_conj
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:09:07.539923+00:00
-- url     : https://prove2.me/theorems/158a8c05-d90f-42ef-9df5-d0b86a434f83
-- title:
--   Row Lev: ext Id mul sup nat Cast conj
-- statement:
--   The Row Lev construction uses the ext Id mul sup nat Cast conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExtIdMulSupNatCastConj.lean#L21-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExtIdMulSupNatCastConj.lean#L21-L62

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IntAfApproxInterUnitConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExtIdMulSupNatCastConj
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

theorem GlobalTheory.RowLev.extId_mul_sup_natCast_conj : ∀ (I : AutInst), (∀ 𝔞 𝔟 : Ideal (𝓞 I.E), extId I (𝔞 * 𝔟) = extId I 𝔞 * extId I 𝔟) ∧ (∀ 𝔞 𝔟 : Ideal (𝓞 I.E), 𝔞 ⊔ 𝔟 = ⊤ → extId I 𝔞 ⊔ extId I 𝔟 = ⊤) ∧ (∀ m : ℕ, extId I (Ideal.span {(m : 𝓞 I.E)}) = Ideal.span {(m : IntAf I.F I.E)}) ∧ (∀ w : HeightOneSpectrum (𝓞 I.E), ∃ w', IsConj I w w') ∧ (∀ w w' : HeightOneSpectrum (𝓞 I.E), IsConj I w w' → IsConj I w' w) ∧ (∀ w w' w'' : HeightOneSpectrum (𝓞 I.E), IsConj I w w' → IsConj I w w'' → w' = w'') ∧ ∀ w w' : HeightOneSpectrum (𝓞 I.E), IsConj I w w' → ∀ z ∈ extId I w.asIdeal, ∃ z' ∈ extId I w'.asIdeal, (z' : (I.E ⊗[I.F] Af I.F)) = Formalism.UG.sigR I.cm.sig (Af I.F) z := by sorry
