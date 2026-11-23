-- Prove2me | Theorems.Thm_GlobalTheory_SmoothForms_SecondKind_sm_iff
-- name    : GlobalTheory.SmoothForms.SecondKind.sm_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:29:06.775367+00:00
-- url     : https://prove2.me/theorems/5a923938-1890-4d12-a290-6f2f925344d3
-- title:
--   Second Kind: sm iff
-- statement:
--   The Second Kind construction uses the sm iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/SmoothInExponentialCoordsIffFirstSecondKind.lean#L219-L343
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/SmoothInExponentialCoordsIffFirstSecondKind.lean#L219-L343

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
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
open NumberField Matrix
open scoped ContDiff Topology
open NormedSpace
variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G}
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem GlobalTheory.SmoothForms.SecondKind.sm_iff (H : _root_.GlobalTheory.SmoothForms.IsLieData σ j s)
    (hl : _root_.GlobalTheory.SmoothForms.HasLog σ j) (T : Set L) (hT : Submodule.span ℝ T = ⊤) (φ : G → ℂ) :
    _root_.GlobalTheory.SmoothForms.Sm (_root_.GlobalTheory.SmoothForms.expMap j s) φ ↔
      ∀ (k : ℕ) (Y : Fin k → L), (∀ i, Y i ∈ T) → ∀ g, ContDiff ℝ ∞ fun t : Fin k → ℝ =>
        φ (g * (List.ofFn fun i => _root_.GlobalTheory.SmoothForms.expMap j s (t i • Y i)).prod) := by sorry
