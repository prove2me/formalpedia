-- Prove2me | Theorems.Thm_GlobalTheory_taylorDir_eq_iff
-- name    : GlobalTheory.taylorDir_eq_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:44:17.944159+00:00
-- url     : https://prove2.me/theorems/c9c12c87-dfcc-4d89-b6a8-9317ac4f4f5e
-- title:
--   Global Theory: taylor Dir eq iff
-- statement:
--   The Global Theory construction uses the taylor Dir eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/MemAnalyticAtZeroOfEventuallyDifferentiableAt.lean#L340-L344
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/MemAnalyticAtZeroOfEventuallyDifferentiableAt.lean#L340-L344

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LineDerivListEqIteratedFDeriv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_MemAnalyticAtZeroOfEventuallyDifferentiableAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory
variable {σ W : Type*} [Fintype σ] [NormedAddCommGroup W] [NormedSpace ℂ W]
variable (u : σ → W) {f g : W → ℂ}

theorem GlobalTheory.taylorDir_eq_iff (hu : Submodule.span ℂ (Set.range u) = ⊤)
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    taylorDir u f = taylorDir u g ↔ f =ᶠ[𝓝 0] g := by sorry
