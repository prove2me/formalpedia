-- Prove2me | Theorems.Thm_GlobalTheory_RealWeil_dRho_mem_weylAlg
-- name    : GlobalTheory.RealWeil.dRho_mem_weylAlg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:54:06.779806+00:00
-- url     : https://prove2.me/theorems/5b9cef2c-4736-4771-bf8f-2e0bcc918efb
-- title:
--   Real Weil: d Rho mem weyl Alg
-- statement:
--   The Real Weil construction uses the d Rho mem weyl Alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IteratedLineDerivMemWeylAlg.lean#L15-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IteratedLineDerivMemWeylAlg.lean#L15-L15

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

theorem GlobalTheory.RealWeil.dRho_mem_weylAlg (w : l ⊕ l → ℝ) : dRho w ∈ weylAlg l := by sorry
