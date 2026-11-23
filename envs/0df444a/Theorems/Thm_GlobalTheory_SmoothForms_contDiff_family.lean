-- Prove2me | Theorems.Thm_GlobalTheory_SmoothForms_contDiff_family
-- name    : GlobalTheory.SmoothForms.contDiff_family
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:40.297679+00:00
-- url     : https://prove2.me/theorems/778d93a2-1d73-4828-a268-9d27f98acfe1
-- title:
--   Smooth Forms: cont Diff family
-- statement:
--   The Smooth Forms construction uses the cont Diff family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/IsLieDataCircle.lean#L37-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/IsLieDataCircle.lean#L37-L80

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ContDiff Topology
open NumberField Matrix
open GlobalTheory GlobalTheory.SmoothForms
variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormedAddCommGroup L] [NormedSpace ℝ L] [Group G]
open scoped ContDiff Topology
open NumberField Matrix
variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormedAddCommGroup L] [NormedSpace ℝ L] [Group G]

theorem GlobalTheory.SmoothForms.contDiff_family [FiniteDimensional ℝ 𝔸] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸}
    {s : 𝔸 → G} (H : _root_.GlobalTheory.SmoothForms.IsLieData σ j s)
    (hl : _root_.GlobalTheory.SmoothForms.HasLog σ j) {φ : G → ℂ}
    (hφ : ∀ g, ContDiffAt ℝ ∞ (fun X : L => φ (g * _root_.GlobalTheory.SmoothForms.expMap j s X)) 0)
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {c : P → 𝔸} (hc : ContDiff ℝ ∞ c)
    (hu : ∀ p, σ (c p) * c p = 1) (g : G) : ContDiff ℝ ∞ fun p => φ (g * s (c p)) := by sorry
