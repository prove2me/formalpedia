-- Prove2me | Theorems.Thm_GlobalTheory_RealWeil_hasDerivAt_inner_rho
-- name    : GlobalTheory.RealWeil.hasDerivAt_inner_rho
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:29:13.380068+00:00
-- url     : https://prove2.me/theorems/97c7e83d-8265-4b9a-babd-eb071d166d8b
-- title:
--   Real Weil: has Deriv At inner rho
-- statement:
--   The Real Weil construction uses the has Deriv At inner rho property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IteratedLineDerivMemWeylAlg.lean#L272-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IteratedLineDerivMemWeylAlg.lean#L272-L292

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

theorem GlobalTheory.RealWeil.hasDerivAt_inner_rho (w : l ⊕ l → ℝ) (φ f : Sch l) :
    HasDerivAt (fun t : ℝ => inner ℂ (φ.toLp 2 volume) (rho (t • w) (f.toLp 2 volume)))
      (inner ℂ (φ.toLp 2 volume) ((dRho w f).toLp 2 volume)) 0 := by sorry
