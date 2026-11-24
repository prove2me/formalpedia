-- Prove2me | Theorems.Thm_GlobalTheory_SmoothForms_DerLinear_der_eq_fderiv
-- name    : GlobalTheory.SmoothForms.DerLinear.der_eq_fderiv
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:18:43.492586+00:00
-- url     : https://prove2.me/theorems/ae7bb076-d2d3-4890-a77d-2655f879a648
-- title:
--   Der Linear: der eq fderiv
-- statement:
--   The Der Linear construction uses the der eq fderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/RightDerivativeAlongLieSmoothAndLinear.lean#L43-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/RightDerivativeAlongLieSmoothAndLinear.lean#L43-L52

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
omit [FiniteDimensional ℝ 𝔸]

theorem GlobalTheory.SmoothForms.DerLinear.der_eq_fderiv {e : L → G} {φ : G → ℂ} (hφ : Sm e φ) (X : L) (g : G) :
    Der e X φ g = fderiv ℝ (fun Z : L => φ (g * e Z)) 0 X := by sorry
