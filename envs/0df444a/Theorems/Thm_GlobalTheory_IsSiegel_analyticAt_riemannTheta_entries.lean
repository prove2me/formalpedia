-- Prove2me | Theorems.Thm_GlobalTheory_IsSiegel_analyticAt_riemannTheta_entries
-- name    : GlobalTheory.IsSiegel.analyticAt_riemannTheta_entries
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:21:59.514573+00:00
-- url     : https://prove2.me/theorems/60f468d8-5e79-4da1-9eb1-24192b262be6
-- title:
--   Is Siegel: analytic At riemann Theta entries
-- statement:
--   The Is Siegel construction uses the analytic At riemann Theta entries property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/HasSumLocallyUniformlyOnIteratedFDerivRiemannThe.lean#L57-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/HasSumLocallyUniformlyOnIteratedFDerivRiemannThe.lean#L57-L64

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

theorem GlobalTheory.IsSiegel.analyticAt_riemannTheta_entries {Ω : Matrix ι ι ℂ} (h : IsSiegel Ω)
    (a b : ι → ℝ) (v : ι → ℂ) :
    AnalyticAt ℂ (fun p : (ι → ℂ) × (ι → ι → ℂ) => riemannTheta a b (of p.2) p.1)
      (v, of.symm Ω) := by sorry
