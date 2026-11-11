-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_NormalHeatResidual_compact_cutoff_matrix
-- name    : OAI.TamingCompatibility.GeometricHilbert.NormalHeatResidual.compact_cutoff_matrix
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:11:42.725205+00:00
-- url     : https://prove2.me/theorems/f5418d63-5c9b-40d2-a36b-2a09d13e461b
-- title:
--   OAI.TamingCompatibility.GeometricHilbert.NormalHeatResidual.compact_cutoff_matrix: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.GeometricHilbert.NormalHeatResidual.compact_cutoff_matrix` of [lean/OAI/Geometry/TamingCompatibility/Concentration/HodgeResidualFamily.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Concentration/HodgeResidualFamily.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility.GeometricHilbert.NormalHeatResidual`, with `open OperatorCalculus FlatHeat Filter Set`, `open scoped Topology ContDiff RealInnerProductSpace`):
--
--   ```lean
--   lemma compact_cutoff_matrix (a : Fin 4 → Fin 4 → P × V → ℝ)
--       (b : Fin 4 → P × V → W →L[ℝ] W) (c : P × V → W →L[ℝ] W)
--       (K : Set P) (hK : IsCompact K) {r : ℝ} (hr : 0 ≤ r)
--       (ha : ∀ x ∈ K ×ˢ Metric.closedBall (0 : V) r, ∀ i j, ContDiffAt ℝ ∞ (a i j) x)
--       (hb : ∀ x ∈ K ×ˢ Metric.closedBall (0 : V) r, ∀ j, ContDiffAt ℝ ∞ (b j) x)
--       (hc : ∀ x ∈ K ×ˢ Metric.closedBall (0 : V) r, ContDiffAt ℝ ∞ c x)
--       (ha0 : ∀ q ∈ K, ∀ i j, a i j (q,0) = euclideanPrincipal i j)
--       (hda0 : ∀ q ∈ K, ∀ i j, fderiv ℝ (fun z => a i j (q,z)) 0 = 0)
--       (hb0 : ∀ q ∈ K, ∀ j, b j (q,0) = 0)
--       (χ : V → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχ0 : χ =ᶠ[𝓝 (0 : V)] 1) :
--       ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ K, ∀ z : V, ‖z‖ ≤ r → ∀ t : ℝ, 0 < t →
--         ‖residual (fun y => CutoffFamilies.principal a χ (q,y))
--           (fun y => CutoffFamilies.first a b χ (q,y))
--           (fun y => CutoffFamilies.zero a b c χ (q,y)) t z‖ ≤ C*heat (2*t) z
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.GeometricHilbert.CutoffFamilies.first`, `OAI.TamingCompatibility.GeometricHilbert.CutoffFamilies.principal`, `OAI.TamingCompatibility.GeometricHilbert.CutoffFamilies.zero`, `OAI.TamingCompatibility.GeometricHilbert.FlatHeat.V`, `OAI.TamingCompatibility.GeometricHilbert.FlatHeat.heat`, `OAI.TamingCompatibility.GeometricHilbert.NormalHeatResidual.End`, `OAI.TamingCompatibility.GeometricHilbert.NormalHeatResidual.euclideanPrincipal` and `OAI.TamingCompatibility.GeometricHilbert.NormalHeatResidual.residual` (definitions bundle `OAIQ239Tc003` of this split).
--
--   **Used by.** The proof of `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.residualCoordinate_gaussian` of this split imports it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Concentration/HodgeResidualFamily.lean (declaration OAI.TamingCompatibility.GeometricHilbert.NormalHeatResidual.compact_cutoff_matrix)

import Mathlib
import Definitions.Def_OAIQ239Tc003

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.NormalHeatResidual
open OperatorCalculus FlatHeat Filter Set
open scoped Topology ContDiff RealInnerProductSpace
variable {P W : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma compact_cutoff_matrix (a : Fin 4 → Fin 4 → P × V → ℝ)
    (b : Fin 4 → P × V → W →L[ℝ] W) (c : P × V → W →L[ℝ] W)
    (K : Set P) (hK : IsCompact K) {r : ℝ} (hr : 0 ≤ r)
    (ha : ∀ x ∈ K ×ˢ Metric.closedBall (0 : V) r, ∀ i j, ContDiffAt ℝ ∞ (a i j) x)
    (hb : ∀ x ∈ K ×ˢ Metric.closedBall (0 : V) r, ∀ j, ContDiffAt ℝ ∞ (b j) x)
    (hc : ∀ x ∈ K ×ˢ Metric.closedBall (0 : V) r, ContDiffAt ℝ ∞ c x)
    (ha0 : ∀ q ∈ K, ∀ i j, a i j (q,0) = euclideanPrincipal i j)
    (hda0 : ∀ q ∈ K, ∀ i j, fderiv ℝ (fun z => a i j (q,z)) 0 = 0)
    (hb0 : ∀ q ∈ K, ∀ j, b j (q,0) = 0)
    (χ : V → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχ0 : χ =ᶠ[𝓝 (0 : V)] 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ K, ∀ z : V, ‖z‖ ≤ r → ∀ t : ℝ, 0 < t →
      ‖residual (fun y => CutoffFamilies.principal a χ (q,y))
        (fun y => CutoffFamilies.first a b χ (q,y))
        (fun y => CutoffFamilies.zero a b c χ (q,y)) t z‖ ≤ C*heat (2*t) z := by
  sorry

end TamingCompatibility.GeometricHilbert.NormalHeatResidual

end
end

end

end OAI
end
