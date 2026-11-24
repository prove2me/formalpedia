-- Prove2me | Theorems.Thm_GlobalTheory_RealWeil_Intertw_eq_of_rhoFun_eq
-- name    : GlobalTheory.RealWeil.Intertw.eq_of_rhoFun_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:15:27.769351+00:00
-- url     : https://prove2.me/theorems/8d56b7a9-abd2-43da-8504-73b05e63e8b6
-- title:
--   Intertw: eq of rho Fun eq
-- statement:
--   The Intertw construction uses the eq of rho Fun eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntertwiningSymplecticAndGroupLaw.lean#L59-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntertwiningSymplecticAndGroupLaw.lean#L59-L99

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzTranslate
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntertwiningSymplecticAndGroupLaw
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.RealWeil MeasureTheory Complex
open scoped SchwartzMap Matrix Real RealInnerProductSpace
open GlobalTheory GlobalTheory.RealWeil GlobalTheory.RealWeil.Intertw
variable {l : Type} [Fintype l]

theorem GlobalTheory.RealWeil.Intertw.eq_of_rhoFun_eq {u u' : l ⊕ l → ℝ} (h : ∀ g : Sch l, rhoFun u ⇑g = rhoFun u' ⇑g) : u = u' := by sorry
