-- Prove2me | Theorems.Thm_GlobalTheory_RealWeil_eq_zero_of_inner_rhoSch_gaussian
-- name    : GlobalTheory.RealWeil.eq_zero_of_inner_rhoSch_gaussian
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:16:42.73562+00:00
-- url     : https://prove2.me/theorems/9a7eaea3-a237-4b18-a5a4-41c7cf1444ab
-- title:
--   Real Weil: eq zero of inner rho Sch gaussian
-- statement:
--   The Real Weil construction uses the eq zero of inner rho Sch gaussian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/EqZeroOfOrthogonalSchrodingerGaussian.lean#L11-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/EqZeroOfOrthogonalSchrodingerGaussian.lean#L11-L62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzTranslate
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EqZeroOfOrthogonalSchrodingerGaussian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.RealWeil MeasureTheory
open scoped SchwartzMap
open scoped FourierTransform RealInnerProductSpace Real
open GlobalTheory GlobalTheory.RealWeil

theorem GlobalTheory.RealWeil.eq_zero_of_inner_rhoSch_gaussian : ∀ (l : Type) [Fintype l] (k : Sch l),
    (∀ w : l ⊕ l → ℝ, inner ℂ ((rhoSch w (GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l))).toLp 2 volume)
      (k.toLp 2 volume) = 0) → k = 0 := by sorry
