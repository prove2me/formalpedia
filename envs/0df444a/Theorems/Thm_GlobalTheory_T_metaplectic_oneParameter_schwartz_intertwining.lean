-- Prove2me | Theorems.Thm_GlobalTheory_T_metaplectic_oneParameter_schwartz_intertwining
-- name    : GlobalTheory.T.metaplectic_oneParameter_schwartz_intertwining
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:35:28.7479+00:00
-- url     : https://prove2.me/theorems/fe4c7859-e10e-4fe4-b6ae-f3efe06e2b25
-- title:
--   T: metaplectic one Parameter schwartz intertwining
-- statement:
--   The T construction uses the metaplectic one Parameter schwartz intertwining property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MetaplecticOneParameterSchwartzIntertwiningStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MetaplecticOneParameterSchwartzIntertwiningStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MetaplecticOneParameterSchwartzIntertwining
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MetaplecticOneParameterSchwartzIntertwiningStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.RealWeil MeasureTheory
open scoped SchwartzMap Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.metaplectic_oneParameter_schwartz_intertwining : GlobalTheory.Published.RealMetaplecticRepresentation → ∀ (l : Type) [Fintype l] [DecidableEq l] [Nonempty l] (X : Matrix (l ⊕ l) (l ⊕ l) ℝ), X ∈ LieAlgebra.Symplectic.sp l ℝ → ∃ U : ℝ → Sch l →ₗ[ℂ] Sch l, (∀ s t f, U (s + t) f = U s (U t f)) ∧ (∀ f, U 0 f = f) ∧ (∀ t w (f f₁ : Sch l), ⇑f₁ = rhoFun w ⇑f → ⇑(U t f₁) = rhoFun (NormedSpace.exp (t • X) *ᵥ w) ⇑(U t f)) ∧ (∀ t f, ∫ x, ‖U t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) ∧ ∀ f y, HasDerivAt (fun t => U t f y) (quad X f y) 0 := by sorry
