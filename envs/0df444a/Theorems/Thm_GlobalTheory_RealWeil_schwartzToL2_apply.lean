-- Prove2me | Theorems.Thm_GlobalTheory_RealWeil_schwartzToL2_apply
-- name    : GlobalTheory.RealWeil.schwartzToL2_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:55:00.43373+00:00
-- url     : https://prove2.me/theorems/8f97b906-54d7-4811-8887-a8328a9a2b86
-- title:
--   Real Weil: schwartz To L2 apply
-- statement:
--   The Real Weil construction uses the schwartz To L2 apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IteratedLineDerivMemWeylAlg.lean#L203-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IteratedLineDerivMemWeylAlg.lean#L203-L203

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

theorem GlobalTheory.RealWeil.schwartzToL2_apply (f : Sch l) : schwartzToL2 l f = f.toLp 2 volume := by sorry
