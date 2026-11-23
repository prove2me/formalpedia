-- Prove2me | Theorems.Thm_GlobalTheory_SmoothForms_SecondKind_map_one_eq
-- name    : GlobalTheory.SmoothForms.SecondKind.map_one_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:47:06.622478+00:00
-- url     : https://prove2.me/theorems/843309f9-4412-4dee-9c39-567836fa3e13
-- title:
--   Second Kind: map one eq
-- statement:
--   The Second Kind construction uses the map one eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/SmoothInExponentialCoordsIffFirstSecondKind.lean#L62-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/SmoothInExponentialCoordsIffFirstSecondKind.lean#L62-L66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_SmoothInExponentialCoordsIffFirstSecondKind
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
noncomputable section
open GlobalTheory GlobalTheory.SmoothForms GlobalTheory.SmoothForms.SecondKind
open NormedSpace
variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G}
open NumberField Matrix
open scoped ContDiff Topology
open NormedSpace
variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G}
omit [FiniteDimensional ℝ 𝔸]

theorem GlobalTheory.SmoothForms.SecondKind.map_one_eq (H : _root_.GlobalTheory.SmoothForms.IsLieData σ j s) : s 1 = 1 := by sorry
