-- Prove2me | Theorems.Thm_OAI_PackingSufficiencySupport_Hamiltonian_AnnularHandleData_normalize_primitive_bp240
-- name    : OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.normalize_primitive_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:55:10.828633+00:00
-- url     : https://prove2.me/theorems/6ad89b6a-8963-4d5e-9263-16011361450d
-- title:
--   OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.normalize_primitive_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.normalize_primitive` of [lean/OAI/Geometry/BallPacking/SurfaceArea/AnnularSecondPositivity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/SurfaceArea/AnnularSecondPositivity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData`, with `open scoped ContDiff Manifold Topology`, `open Set Function Manifold`, `open MeasureTheory`):
--
--   ```lean
--   theorem normalize_primitive_bp240
--       (D : AnnularHandleData E M) {V : Set P} (hV : IsOpen V) {b : ℝ} (hb : b<D.width)
--       {Γ N : P → ManifoldOneForm E M}
--       (hΓ : ∀ c,ContDiffOn ℝ ∞ (fun q : P × E => chartOneForm (Γ q.1) c q.2)
--         (V ×ˢ (extChartAt 𝓘(ℝ,E) c).target))
--       (hN : ∀ p∈V,∀ x∈D.chart.target,ContDiffAt ℝ ∞
--         (fun q : P × E => chartOneForm (N q.1) x q.2) (p,extChartAt 𝓘(ℝ,E) x x))
--       (hcurv : ∀ p∈V,∀ x∈D.chart.target,
--         manifoldExteriorOneForm (Γ p) x=manifoldExteriorOneForm (N p) x) :
--       ∃ (Γ₁ : P → ManifoldOneForm E M) (L W : Set M),
--         IsCompact L ∧ L⊆D.chart.target ∧ IsOpen W ∧
--         D.chart '' band b⊆W ∧ W⊆D.chart.target ∧
--         (∀ c,ContDiffOn ℝ ∞ (fun q : P × E => chartOneForm (Γ₁ q.1) c q.2)
--           (V ×ˢ (extChartAt 𝓘(ℝ,E) c).target)) ∧
--         (∀ p,support (Γ₁ p-Γ p)⊆tsupport D.dual∪L) ∧
--         (∀ p,HasCompactSupport (Γ₁ p-Γ p)) ∧
--         (∀ p∈V,∀ x,manifoldExteriorOneForm (Γ₁ p) x=manifoldExteriorOneForm (Γ p) x) ∧
--         (∀ p∈V,∀ x∈W,Γ₁ p x=N p x)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PackingSufficiencySupport.Hamiltonian.CircleModel`, `OAI.PackingSufficiencySupport.Hamiltonian.CylinderModel`, `OAI.PackingSufficiencySupport.Hamiltonian.HandleCylinder`, `OAI.PackingSufficiencySupport.Hamiltonian.ManifoldOneForm`, `OAI.PackingSufficiencySupport.Hamiltonian.chartOneForm`, `OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace` and `OAI.PackingSufficiencySupport.Hamiltonian.manifoldExteriorOneForm` (definitions bundle `OAIQ240Bp003` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData` (definitions bundle `OAIQ240Bp015` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.band` (definitions bundle `OAIQ240Bp019` of this split).
--
--   **Used by.** The proof of `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.exists_surface_step_two_bp240` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/SurfaceArea/AnnularSecondPositivity.lean (declaration OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.normalize_primitive)

import Mathlib
import Definitions.Def_OAIQ240Bp019

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian.AnnularHandleData
open scoped ContDiff Manifold Topology
open Set Function Manifold
open MeasureTheory

variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [NormalSpace M] [SigmaCompactSpace M]

theorem normalize_primitive_bp240
    (D : AnnularHandleData E M) {V : Set P} (hV : IsOpen V) {b : ℝ} (hb : b<D.width)
    {Γ N : P → ManifoldOneForm E M}
    (hΓ : ∀ c,ContDiffOn ℝ ∞ (fun q : P × E => chartOneForm (Γ q.1) c q.2)
      (V ×ˢ (extChartAt 𝓘(ℝ,E) c).target))
    (hN : ∀ p∈V,∀ x∈D.chart.target,ContDiffAt ℝ ∞
      (fun q : P × E => chartOneForm (N q.1) x q.2) (p,extChartAt 𝓘(ℝ,E) x x))
    (hcurv : ∀ p∈V,∀ x∈D.chart.target,
      manifoldExteriorOneForm (Γ p) x=manifoldExteriorOneForm (N p) x) :
    ∃ (Γ₁ : P → ManifoldOneForm E M) (L W : Set M),
      IsCompact L ∧ L⊆D.chart.target ∧ IsOpen W ∧
      D.chart '' band b⊆W ∧ W⊆D.chart.target ∧
      (∀ c,ContDiffOn ℝ ∞ (fun q : P × E => chartOneForm (Γ₁ q.1) c q.2)
        (V ×ˢ (extChartAt 𝓘(ℝ,E) c).target)) ∧
      (∀ p,support (Γ₁ p-Γ p)⊆tsupport D.dual∪L) ∧
      (∀ p,HasCompactSupport (Γ₁ p-Γ p)) ∧
      (∀ p∈V,∀ x,manifoldExteriorOneForm (Γ₁ p) x=manifoldExteriorOneForm (Γ p) x) ∧
      (∀ p∈V,∀ x∈W,Γ₁ p x=N p x) := by
  sorry

end PackingSufficiencySupport.Hamiltonian.AnnularHandleData
end

end OAI
end
