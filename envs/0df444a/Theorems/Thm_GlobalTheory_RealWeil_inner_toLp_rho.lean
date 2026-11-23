-- Prove2me | Theorems.Thm_GlobalTheory_RealWeil_inner_toLp_rho
-- name    : GlobalTheory.RealWeil.inner_toLp_rho
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:29:28.064397+00:00
-- url     : https://prove2.me/theorems/c5d5f1e9-2d8d-40c7-924e-a67553b3d06a
-- title:
--   Real Weil: inner to Lp rho
-- statement:
--   The Real Weil construction uses the inner to Lp rho property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IteratedLineDerivMemWeylAlg.lean#L263-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IteratedLineDerivMemWeylAlg.lean#L263-L268

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

theorem GlobalTheory.RealWeil.inner_toLp_rho (w : l ⊕ l → ℝ) (φ f : Sch l) :
    inner ℂ (φ.toLp 2 volume) (rho w (f.toLp 2 volume)) = ∫ x, inner ℂ (φ x) (rhoFun w f x) := by sorry
