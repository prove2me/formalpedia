-- Prove2me | Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_homotopy_affine_error_energy
-- name    : OAI.HigherDimensionalBallPacking.Rigidity.homotopy_affine_error_energy
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T16:47:51.778218+00:00
-- url     : https://prove2.me/theorems/8a0d8940-4f42-41f8-84e5-623abd1deac2
-- title:
--   OAI.HigherDimensionalBallPacking.Rigidity.homotopy_affine_error_energy: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.packing_necessity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HigherDimensionalBallPacking.Rigidity.homotopy_affine_error_energy` of [lean/OAI/Geometry/BallPacking/BallPacking/Necessity/AffineEnergy.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Necessity/AffineEnergy.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HigherDimensionalBallPacking.Rigidity`, with `open scoped ContDiff Topology`, `open Set Function Filter`, `open scoped ContDiff Topology Manifold`, `open Set Function Filter MeasureTheory`, `open Set Function MeasureTheory`, `open Set Function`, `open SymplecticBallPacking.Hamiltonian (Plane planarCurl)`, `open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)`, `open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)`, `open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)`, `open SymplecticBallPacking.Hamiltonian`, `open SymplecticBallPacking.Hamiltonian (Plane)`, `open Set Filter Function`, `open Set Filter MeasureTheory`, `open scoped Topology`, `open Set Filter Finset`, `open scoped ContDiff Topology Classical`, `open Set Filter`, `open scoped BoundedContinuousFunction ContDiff Topology`, `open Set Function Filter Topology`, `open scoped NNReal`, `open scoped ContDiff Topology BoundedContinuousFunction`, `open Function`, `open scoped Topology ContDiff`, `open scoped ContDiff Topology`, `open Set Function Filter MeasureTheory`, `open SymplecticBallPacking.Hamiltonian`):
--
--   ```lean
--   theorem homotopy_affine_error_energy (n : ℕ) (_hn : 3 ≤ n)
--       (J : Phase n → End n) (hJs : ContDiff ℝ ∞ J)
--       (hJ : ∀ x, Compatible (J x))
--       (hc : HasCompactSupport (fun x => J x-standardJ n))
--       (hs : tsupport (fun x => J x-standardJ n) ⊆ openBall n 1)
--       (p q : Phase n) (_hpq : p ≠ q) :
--       ∃ C > 0, ∀ t ∈ Icc (0:ℝ) 1, ∀ u : ℂ → Phase n,
--         AffineLineCurve (lineHomotopy J t) p q u →
--         ∃ v : Phase n, v ≠ 0 ∧
--           Tendsto (fun z : ℂ => z⁻¹ • u z) (cocompact ℂ) (𝓝 v) ∧
--           Integrable (dirichletDensity (fun z : ℂ => u z-z • v)) ∧
--           (∫ z, dirichletDensity (fun z : ℂ => u z-z • v) z) ≤ C
--   ```
--
--   **Definitions.** The statement is written with `OAI.HigherDimensionalBallPacking.Rigidity.Compatible`, `OAI.HigherDimensionalBallPacking.Rigidity.End`, `OAI.HigherDimensionalBallPacking.Rigidity.standardJ` and `OAI.SymplecticBallPacking.Hamiltonian.Plane` (definitions bundle `OAIQ10Bp000` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.AffineLineCurve` (definitions bundle `OAIQ10Bp002` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.lineHomotopy` (definitions bundle `OAIQ10Bp003` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.dirichletDensity` (definitions bundle `OAIQ10Bp005` of this split); `OAI.HigherDimensionalBallPacking.Phase` and `OAI.HigherDimensionalBallPacking.openBall` (the published bundle `Def_BallPackingNecessity`).
--
--   **Used by.** The proofs of `OAI.HigherDimensionalBallPacking.Rigidity.homotopy_C0_compactness`, `OAI.HigherDimensionalBallPacking.Rigidity.homotopy_common_affine_carrier`, `OAI.HigherDimensionalBallPacking.Rigidity.homotopy_density_common_support`, `OAI.HigherDimensionalBallPacking.Rigidity.homotopy_limit_has_nonzero_asymptotic` and `OAI.HigherDimensionalBallPacking.Rigidity.homotopy_slopes_bounded_above` of this split import it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Necessity/AffineEnergy.lean (declaration OAI.HigherDimensionalBallPacking.Rigidity.homotopy_affine_error_energy)

import Mathlib
import Definitions.Def_BallPackingNecessity
import Definitions.Def_OAIQ10Bp005

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian
namespace HigherDimensionalBallPacking.Rigidity

theorem homotopy_affine_error_energy (n : ℕ) (_hn : 3 ≤ n)
    (J : Phase n → End n) (hJs : ContDiff ℝ ∞ J)
    (hJ : ∀ x, Compatible (J x))
    (hc : HasCompactSupport (fun x => J x-standardJ n))
    (hs : tsupport (fun x => J x-standardJ n) ⊆ openBall n 1)
    (p q : Phase n) (_hpq : p ≠ q) :
    ∃ C > 0, ∀ t ∈ Icc (0:ℝ) 1, ∀ u : ℂ → Phase n,
      AffineLineCurve (lineHomotopy J t) p q u →
      ∃ v : Phase n, v ≠ 0 ∧
        Tendsto (fun z : ℂ => z⁻¹ • u z) (cocompact ℂ) (𝓝 v) ∧
        Integrable (dirichletDensity (fun z : ℂ => u z-z • v)) ∧
        (∫ z, dirichletDensity (fun z : ℂ => u z-z • v) z) ≤ C := by
  sorry

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end
