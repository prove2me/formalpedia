-- Prove2me | Theorems.Thm_GlobalTheory_RealWeil_hasDerivAt_rhoFun_at
-- name    : GlobalTheory.RealWeil.hasDerivAt_rhoFun_at
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:15:56.769884+00:00
-- url     : https://prove2.me/theorems/2c2d2eed-d203-4a44-8bc0-e3e853d7c4f9
-- title:
--   Real Weil: has Deriv At rho Fun at
-- statement:
--   The Real Weil construction uses the has Deriv At rho Fun at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IteratedLineDerivMemWeylAlg.lean#L247-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IteratedLineDerivMemWeylAlg.lean#L247-L260

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap LineDeriv Matrix
open scoped Real RealInnerProductSpace ContDiff FourierTransform
open GlobalTheory GlobalTheory.RealWeil
variable {l : Type} [Fintype l]
variable [DecidableEq l]
omit [DecidableEq l]

theorem GlobalTheory.RealWeil.hasDerivAt_rhoFun_at (w : l ⊕ l → ℝ) (f : Sch l) (x : EuclideanSpace ℝ l) (t : ℝ) :
    HasDerivAt (fun t : ℝ => rhoFun (t • w) f x) (rhoFun (t • w) (dRho w f) x) t := by sorry
