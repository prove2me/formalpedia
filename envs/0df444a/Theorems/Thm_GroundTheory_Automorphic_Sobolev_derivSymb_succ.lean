-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_derivSymb_succ
-- name    : GroundTheory.Automorphic.Sobolev.derivSymb_succ
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:59:29.960341+00:00
-- url     : https://prove2.me/theorems/48f6f28b-fb89-590c-8fce-5397d22a2765
-- title:
--   Sobolev: deriv Symb succ
-- statement:
--   The Sobolev construction uses the deriv Symb succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L289-L291
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L289-L291

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem GroundTheory.Automorphic.Sobolev.derivSymb_succ {k : ℕ} (w : Fin (k + 1) → E) (ξ : E) :
    derivSymb w ξ = derivSymb (Fin.tail w) ξ * ((2 * Real.pi * Complex.I) * ((inner ℝ ξ (w 0) : ℝ) : ℂ)) := by sorry
