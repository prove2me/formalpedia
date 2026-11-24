-- Prove2me | Theorems.Thm_Moise_polygonal_schoenflies_2d_disk
-- name    : Moise.polygonal_schoenflies_2d_disk
-- status  : Open
-- author  : @wojtek_politarczyk
-- created : 2026-11-24T21:15:57.092639+00:00
-- url     : https://prove2.me/theorems/3fe38805-b05a-4de3-87f2-e614e5d7b7e9
-- title:
--   Polygonal 2D Schoenflies theorem (closed disk form)
-- statement:
--   Let $P$ be a finite $1$-dimensional Euclidean complex in $\mathbb{R}^2$ with $|P| \simeq S^1$, and let $U \subset \mathbb{R}^2 \setminus |P|$ be its bounded open connected complementary component with frontier $|P|$. Then $\overline{U}$ is triangulated by a Euclidean complex $K_{\mathrm{in}}$ in $\mathbb{R}^2$ that is PL-homeomorphic to the standard $2$-simplex $\Delta^2 = \operatorname{conv}\{(0,0), (1,0), (0,1)\}$, mapping $|P|$ onto $\partial \Delta^2$.
-- source:
--   E. E. Moise, Geometric Topology in Dimensions 2 and 3, Springer GTM 47, 1977, Chapter 3.

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Hull
import Mathlib.Topology.Connected.Basic
import Definitions.Def_Moise_EuclideanComplex

namespace Moise

theorem polygonal_schoenflies_2d_disk (P : EuclideanComplex 2)
    (hfin : P.IsFinite) (hdim : ∀ σ ∈ P.simplices, σ.dim ≤ 1)
    (hS1 : Nonempty (P.polyhedron ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1))
    (inside : Set (EuclideanSpace ℝ (Fin 2)))
    (hinside_open : IsOpen inside) (hinside_conn : IsConnected inside)
    (hinside_bdd : Bornology.IsBounded inside)
    (hinside_fr : frontier inside = P.polyhedron)
    (hinside_sub : inside ⊆ P.polyhedronᶜ) :
    ∃ (K_in K_Δ : EuclideanComplex 2),
      K_in.polyhedron = closure inside ∧
      K_Δ.polyhedron = convexHull ℝ
        ({(0 : EuclideanSpace ℝ (Fin 2)),
          (WithLp.equiv 2 (Fin 2 → ℝ)).symm ![1, 0],
          (WithLp.equiv 2 (Fin 2 → ℝ)).symm ![0, 1]} : Set (EuclideanSpace ℝ (Fin 2))) ∧
      ∃ f : K_in.polyhedron ≃ₜ K_Δ.polyhedron,
        IsPLHomeomorph K_in K_Δ f ∧
        Subtype.val '' (f '' (Subtype.val ⁻¹' P.polyhedron)) =
          frontier (convexHull ℝ
            ({(0 : EuclideanSpace ℝ (Fin 2)),
              (WithLp.equiv 2 (Fin 2 → ℝ)).symm ![1, 0],
              (WithLp.equiv 2 (Fin 2 → ℝ)).symm ![0, 1]} : Set (EuclideanSpace ℝ (Fin 2)))) := by sorry

end Moise
