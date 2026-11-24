-- Prove2me | Theorems.Thm_GlobalTheory_differentiable_riemannThetaTerm
-- name    : GlobalTheory.differentiable_riemannThetaTerm
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:15:50.899056+00:00
-- url     : https://prove2.me/theorems/1418819e-89b4-44cb-a280-556915a51d24
-- title:
--   Global Theory: differentiable riemann Theta Term
-- statement:
--   The Global Theory construction uses the differentiable riemann Theta Term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/HasSumLocallyUniformlyOnIteratedFDerivRiemannThe.lean#L44-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/HasSumLocallyUniformlyOnIteratedFDerivRiemannThe.lean#L44-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LineDerivListEqIteratedFDeriv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HasSumLocallyUniformlyOnIteratedFDerivRiemannThe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped Real
noncomputable section
open GlobalTheory
variable {ι : Type*} [Fintype ι]

theorem GlobalTheory.differentiable_riemannThetaTerm (a b : ι → ℝ) (n : ι → ℤ) :
    Differentiable ℂ fun p : (ι → ℂ) × (ι → ι → ℂ) => riemannThetaTerm a b (of p.2) p.1 n := by sorry
