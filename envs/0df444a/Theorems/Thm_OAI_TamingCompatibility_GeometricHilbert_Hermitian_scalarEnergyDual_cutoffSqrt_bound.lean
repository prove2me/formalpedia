-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_Hermitian_scalarEnergyDual_cutoffSqrt_bound
-- name    : OAI.TamingCompatibility.GeometricHilbert.Hermitian.scalarEnergyDual_cutoffSqrt_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:30:22.131824+00:00
-- url     : https://prove2.me/theorems/7de01823-af84-41e7-b439-6b54ff90d56e
-- title:
--   OAI.TamingCompatibility.GeometricHilbert.Hermitian.scalarEnergyDual_cutoffSqrt_bound: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.GeometricHilbert.Hermitian.scalarEnergyDual_cutoffSqrt_bound` of [lean/OAI/Geometry/TamingCompatibility/Functional/HermitianCutoffDualBounds.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Functional/HermitianCutoffDualBounds.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility.GeometricHilbert.Hermitian`, with `open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume`, `open Set Filter ComplexMatrix _root_.MeasureTheory EuclideanSobolevOperators RadialPotential`, `open scoped Manifold ContDiff Topology SchwartzMap LineDeriv RealInnerProductSpace`):
--
--   ```lean
--   theorem scalarEnergyDual_cutoffSqrt_bound
--       (p : A.centers) (τ : 𝓢(Space,ℝ))
--       (K : Set Space) (hK : IsCompact K) (hKD : K ⊆ (D p).domain)
--       (hτ : ∀ z ∈ K, τ z * coordinateWeight A p z = 1)
--       (V : Space → Space) (hV : ContDiff ℝ ∞ V)
--       (R : ℝ) (hR : 0 < R)
--       (K₀ : Set Space) (hK₀ : IsCompact K₀)
--       (hcenters : ∀ b ∈ K₀, Metric.closedBall b (2*R) ⊆ K) :
--       ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : Fin 2) s, ∀ hsr : s ∈ Ioc (0:ℝ) (2*R), ∀ b, ∀ hb : b ∈ K₀,
--         ‖scalarEnergyDualLM A J α hs ht D p K hK hKD j
--           (HermitianRadial.sqrtCutoffSourceSupported W V hV hR hsr.1 K b (hcenters b hb))‖ ≤ C
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.ManifoldLocalization.FiniteCharts` (definitions bundle `OAIQ239Tc003` of this split); `OAI.TamingCompatibility.supportedSchwartz` (definitions bundle `OAIQ239Tc004` of this split); `OAI.TamingCompatibility.GeometricChart.Data` and `OAI.TamingCompatibility.GeometricChart.Data.source` (definitions bundle `OAIQ239Tc011` of this split); `OAI.TamingCompatibility.HermitianRadial.sqrtCutoffSourceSupported` (definitions bundle `OAIQ239Tc012` of this split); `OAI.TamingCompatibility.GeometricChart.coordinateWeight`, `OAI.TamingCompatibility.GeometricHilbert.L2`, `OAI.TamingCompatibility.GeometricHilbert.PreL2`, `OAI.TamingCompatibility.GeometricHilbert.preL2Add`, `OAI.TamingCompatibility.GeometricHilbert.preL2Inner`, `OAI.TamingCompatibility.GeometricHilbert.preL2Module` and `OAI.TamingCompatibility.GeometricHilbert.preL2Normed` (definitions bundle `OAIQ239Tc014` of this split); `OAI.TamingCompatibility.GeometricHilbert.antiEnergy` (definitions bundle `OAIQ239Tc025` of this split); `OAI.TamingCompatibility.GeometricHilbert.scalarEnergyDualLM` (definitions bundle `OAIQ239Tc029` of this split); `OAI.TamingCompatibility.AlmostComplexStructure`, `OAI.TamingCompatibility.IsSmooth`, `OAI.TamingCompatibility.Model`, `OAI.TamingCompatibility.Space`, `OAI.TamingCompatibility.Tames` and `OAI.TamingCompatibility.TwoForm` (the published bundle `Def_TamingCompatibility`).
--
--   **Used by.** The proof of `OAI.TamingCompatibility.GeometricHilbert.Hermitian.combinedForm_global_lower` of this split imports it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Functional/HermitianCutoffDualBounds.lean (declaration OAI.TamingCompatibility.GeometricHilbert.Hermitian.scalarEnergyDual_cutoffSqrt_bound)

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc029

section

attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter ComplexMatrix _root_.MeasureTheory EuclideanSobolevOperators RadialPotential
open scoped Manifold ContDiff Topology SchwartzMap LineDeriv RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

variable (W : Space → Space →L[ℝ] Space) (hW : ContDiff ℝ ∞ W)

include hD hW in

theorem scalarEnergyDual_cutoffSqrt_bound
    (p : A.centers) (τ : 𝓢(Space,ℝ))
    (K : Set Space) (hK : IsCompact K) (hKD : K ⊆ (D p).domain)
    (hτ : ∀ z ∈ K, τ z * coordinateWeight A p z = 1)
    (V : Space → Space) (hV : ContDiff ℝ ∞ V)
    (R : ℝ) (hR : 0 < R)
    (K₀ : Set Space) (hK₀ : IsCompact K₀)
    (hcenters : ∀ b ∈ K₀, Metric.closedBall b (2*R) ⊆ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : Fin 2) s, ∀ hsr : s ∈ Ioc (0:ℝ) (2*R), ∀ b, ∀ hb : b ∈ K₀,
      ‖scalarEnergyDualLM A J α hs ht D p K hK hKD j
        (HermitianRadial.sqrtCutoffSourceSupported W V hV hR hsr.1 K b (hcenters b hb))‖ ≤ C := by
  sorry

end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end
end

end OAI
end
