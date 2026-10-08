-- Prove2me | Theorems.Thm_OAI_SmoothLocal_Geometry_exists_local_metric_without_local_immersion
-- name    : OAI.SmoothLocal.Geometry.exists_local_metric_without_local_immersion
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:22.802352+00:00
-- url     : https://prove2.me/theorems/ac8f0ec6-a13e-4856-9592-ed3937bc9cc1
-- statement:
--   The theorem states that there exists a Riemannian metric on the open square (-1,1)² in the plane ℝ², given as a matrix-valued function g assigning to each point of the square a 2×2 real matrix, such that g is smooth in every entry (C^∞) and positive definite at every point, yet no smooth local isometric immersion into three-dimensional Euclidean space exists near the origin. Precisely, for every open set U of ℝ² that is contained in the square and contains the origin 0, and for every map F from U to ℝ³ (with the Euclidean inner product), it is not the case that F is C^∞ and satisfies, at every point p of U and for all vectors v and w in ℝ², the equality ⟨dF_p(v), dF_p(w)⟩ = vᵀ g(p) w, where dF_p is the manifold derivative of F at p. In other words, the pullback of the Euclidean metric by F never equals g on any such neighborhood of the origin.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/IsometricImmersion.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/IsometricImmersion.lean; bytes 1250..1904
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Definitions.Def_IsometricImmersion

namespace OAI

noncomputable section

open Set TopologicalSpace

open scoped ContDiff Topology Manifold Matrix

namespace SmoothLocal.Geometry

theorem exists_local_metric_without_local_immersion :
    ∃ g : coordinateSquareOpen → Matrix (Fin 2) (Fin 2) ℝ,
      LocalSmoothPositive coordinateSquareOpen g ∧
      ∀ U : Opens Coord, ∀ hUS : (U : Set Coord) ⊆ square,
        (0 : Coord) ∈ U → ∀ F : U → Ambient,
          ¬ (ContMDiff 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) ∞ F ∧
            ∀ p : U, ∀ v w : Coord,
              (inner ℝ : Ambient → Ambient → ℝ) (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) F p v)
                (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) F p w) =
                  v ⬝ᵥ (g ⟨p, hUS p.property⟩ *ᵥ w)) := by
  sorry

end SmoothLocal.Geometry
end
end OAI
