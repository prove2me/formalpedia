-- Prove2me | Theorems.Thm_GlobalTheory_SmoothForms_DerLinear_contDiff_exp
-- name    : GlobalTheory.SmoothForms.DerLinear.contDiff_exp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:45.637852+00:00
-- url     : https://prove2.me/theorems/92b42212-b2e0-428f-840b-a9b97c04d636
-- title:
--   Der Linear: cont Diff exp
-- statement:
--   The Der Linear construction uses the cont Diff exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/RightDerivativeAlongLieSmoothAndLinear.lean#L35-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/RightDerivativeAlongLieSmoothAndLinear.lean#L35-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_RightDerivativeAlongLieSmoothAndLinear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
open GlobalTheory GlobalTheory.SmoothForms GlobalTheory.SmoothForms.DerLinear
variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G}

theorem GlobalTheory.SmoothForms.DerLinear.contDiff_exp (H : IsLieData σ j s) : ContDiff ℝ ∞ fun X : L => NormedSpace.exp (j X) := by sorry
