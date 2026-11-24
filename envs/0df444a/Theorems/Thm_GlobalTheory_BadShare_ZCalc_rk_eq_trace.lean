-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_ZCalc_rk_eq_trace
-- name    : GlobalTheory.BadShare.ZCalc.rk_eq_trace
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:59:46.175526+00:00
-- url     : https://prove2.me/theorems/aab47335-f42e-4beb-9335-dabae0a9dbdf
-- title:
--   ZCalc: rk eq trace
-- statement:
--   The ZCalc construction uses the rk eq trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CentralIdempotentIrreducibleCharacterProps.lean#L53-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CentralIdempotentIrreducibleCharacterProps.lean#L53-L59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_StandardFiveNontrivial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CharacterIdempotents_Scalar
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CentralIdempotentIrreducibleCharacterProps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.BadShare GlobalTheory.BadShare.ZCalc
variable {G : Type} [Group G] [Fintype G]

theorem GlobalTheory.BadShare.ZCalc.rk_eq_trace {M : Type} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ G M)
    (e : G → ℂ) (he : conv e e = e) : (rk ρ e : ℂ) = ∑ γ, e γ * LinearMap.trace ℂ M (ρ γ) := by sorry
