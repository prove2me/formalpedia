-- Prove2me | Theorems.Thm_OAI_Solenoidal_sheet_theorem
-- name    : OAI.Solenoidal.sheet_theorem
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:24.319981+00:00
-- url     : https://prove2.me/theorems/c10e2bb3-9888-42e7-b815-6ef88c1d48fc
-- statement:
--   The theorem states that, for any natural number N, any sheet datum D of size N, and any computable real viscosity ν>0, there exist a forcing field f and a velocity field u (each a time-dependent vector field on ℝ³) and a flow map X such that the following hold. Here D consists of N source rectangles and N target rectangles with rational corners, all inside the square [2,3]², with the sources pairwise separated by a positive distance and likewise the targets, together with positive rational ratios in each of two coordinates such that the diagonal affine map from source i to target i, which sends the source center to the target center and scales offsets by the ratios, maps the source rectangle exactly onto the target rectangle. Both f and u are periodic in space with period 10 in every coordinate and are C^∞ in space and time jointly. The forcing f is effective, meaning that all its mixed space-time partial derivatives can be approximated to any rational accuracy by a single fixed partial recursive procedure from computable names of the evaluation point. Moreover f has zero mean over the fundamental cell [0,10)³ at every time, is divergence free, and is 1-periodic in time. The field u is a classical solution on t≥0 of the forced Navier–Stokes equations ∂ₜu + (u·∇)u = −∇p + ν Δu + f with zero pressure, zero initial data, incompressibility and spatial periodicity, so u is a solution driven by f without pressure. Any classical solution v with pressure p for the same f and ν and with zero initial velocity coincides with u, and has p identically zero, for all t≥0. The flow map X satisfies X(0,a)=a and solves the particle-path equation dX/dt=u(t,X) for t≥0, and for each i and each point y of the i-th source rectangle, the time-1 flow image of the sheet point (y₀,y₁,2) agrees modulo the torus ℝ³/(10ℤ)³ with the sheet point at the diagonal-map image of y. Further, u vanishes in a neighborhood of every integer time, the advection term (u·∇)u vanishes everywhere, and both f and u have all their mixed space-time derivatives uniformly bounded by rational bounds computable from the derivative multi-index by a fixed partial recursive procedure. Finally, if N=0 then f and u are identically zero.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SolenoidalSheetPrograms.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SolenoidalSheetPrograms.lean; bytes 6448..7323
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_SolenoidalSheetPrograms

namespace OAI

noncomputable section

open Set MeasureTheory

open scoped BigOperators

namespace Solenoidal

theorem sheet_theorem {N : ℕ} (D : SheetData N) (ν : ℝ)
    (hν : 0 < ν) (hνcomp : ComputableReal ν) :
    ∃ f u : Field, ∃ X : ℝ → Space → Space,
      SpatiallyPeriodic f ∧ SpatiallyPeriodic u ∧
      Smooth f ∧ Smooth u ∧ Effective f ∧
      MeanZero f ∧ DivergenceFree f ∧ OnePeriodic f ∧
      ClassicalSolution ν f u (fun _ _ => 0) ∧
      (∀ v : Field, ∀ p : Pressure, ClassicalSolution ν f v p →
        ∀ t, 0 ≤ t → ∀ x, v t x = u t x ∧ p t x = 0) ∧
      MaterialFlow u X ∧
      (∀ i : Fin N, ∀ y ∈ (D.source i).carrier,
        toTorus (X 1 (sheet y)) =
          toTorus (sheet (diagonalMap (D.source i) (D.target i) (D.ratio i) y))) ∧
      IntegerCollars u ∧ (∀ t x, advection u t x = 0) ∧
      EffectiveBounds f ∧ EffectiveBounds u ∧
      (N = 0 → f = 0 ∧ u = 0) := by
  sorry

end Solenoidal
end
end OAI
