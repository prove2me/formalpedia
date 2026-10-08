-- Prove2me | Theorems.Thm_OAI_Tingley_tingley_sphere_isometry_full
-- name    : OAI.Tingley.tingley_sphere_isometry_full
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:32.432498+00:00
-- url     : https://prove2.me/theorems/58608ed6-6906-48c2-a08e-1e7f99726aec
-- statement:
--   The theorem states that, for real Banach spaces X and Y that are both nontrivial (complete normed real vector spaces), if f is a distance-preserving map from the unit sphere of X (vectors of norm 1) to the unit sphere of Y, and f is surjective, then there exists a linear isometric equivalence T from X onto Y with several properties. T agrees with f on the unit sphere, T(u)=f(u) for every unit vector u; T sends 0 to 0; for every nonzero x, T(x)=‖x‖·f(x/‖x‖), where x/‖x‖ is the normalization of x onto the unit sphere; and T is surjective. Moreover, T is the only real-linear extension of f: any real-linear map L from X to Y that agrees with f on every unit vector must equal the linear map underlying T.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/TingleySphereIsometry.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/TingleySphereIsometry.lean; bytes 495..1259
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Topology.MetricSpace.Isometry
import Definitions.Def_TingleySphereIsometry

namespace OAI

noncomputable section

namespace Tingley

universe u v

variable {X : Type u} {Y : Type v}

variable [NormedAddCommGroup X] [NormedSpace ℝ X]

variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Radial formula, surjectivity, and uniqueness among all real-linear extensions. -/
theorem tingley_sphere_isometry_full
    {X : Type u} {Y : Type v}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [Nontrivial X] [Nontrivial Y]
    (f : UnitSphere X → UnitSphere Y) (hf : Isometry f) (hs : Function.Surjective f) :
    ∃ T : X ≃ₗᵢ[ℝ] Y,
      (∀ u : UnitSphere X, T (u : X) = (f u : Y)) ∧
      T 0 = 0 ∧
      (∀ x : X, ∀ hx : x ≠ 0, T x = ‖x‖ • (f (normalize x hx) : Y)) ∧
      Function.Surjective T ∧
      (∀ L : X →ₗ[ℝ] Y, (∀ u : UnitSphere X, L (u : X) = (f u : Y)) →
        L = T.toLinearEquiv.toLinearMap) := by
  sorry

end Tingley
end
end OAI
