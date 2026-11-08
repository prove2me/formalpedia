-- Prove2me | Theorems.Thm_Grunbaum2003_rayFrame_boundary_extension_axes_and_cramer_normal
-- name    : Grunbaum2003.rayFrame_boundary_extension_axes_and_cramer_normal
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-07T18:41:14.981205+00:00
-- url     : https://prove2.me/theorems/98af2447-276a-4154-a056-68ff1453efd7
-- title:
--   Section-induced ray oracle, boundary frame extension, transverse coordinate axes, and Cramer facet normal recovery
-- statement:
--   This theorem formalizes the higher-dimensional boundary-frame growth and Cramer normal recovery steps of the Gritzmann–Klee–Westwater ray-oracle reconstruction algorithm:
--
--   1. **Section-induced ray oracle (`induced_rayOracle_of_leftInverse`):** If $P = \{x \in \mathbb{R}^d \mid \forall j, L_j(x) \le 1\}$ and $f : \mathbb{R}^n \to \mathbb{R}^d$ has a continuous linear left inverse $g$, then $r \mapsto g(\operatorname{oracle}(f(r)))$ is a valid ray oracle for $f^{-1}(P)$ and satisfies $f(g(\operatorname{oracle}(f(r)))) = \operatorname{oracle}(f(r))$ for all $r \neq 0$.
--   2. **Transverse coordinate axis and off-axis pivot (`exists_coordinate_axis_outside_frame`, `exists_off_axis_pivot`):** Every linearly independent boundary frame $v : \operatorname{Fin} n \to \mathbb{R}^d$ of size $n < d$ admits a standard coordinate axis $e_i \notin \operatorname{span}(v)$, and every nonzero $p \in \operatorname{span}(v)$ has an off-axis coordinate $j \neq i$ with $p_j \neq 0$ (providing the pivot for `sectionQueryProgram`).
--   3. **Positive boundary frame extension (`extend_positive_boundary_frame`):** Given an independent frame $v : \operatorname{Fin} n \to \mathbb{R}^d$ in $P$ with positive convex combination $p = \sum_i w_i v_i$ and a new boundary point $q \in P \setminus \operatorname{span}(v)$ sharing a defining support row $L_j(p) = L_j(q) = 1$, prepending $q$ yields an independent frame $V = \operatorname{Fin.cons}(q, v)$ in $P$ and midpoint $p' = \frac{1}{2}(p + q) \in \operatorname{frontier}(P)$ such that every active row $L_k(p') = 1$ contains the entire enlarged frame ($L_k(V_i) = 1$).
--   4. **Cramer facet normal recovery (`frameNormal_eq_original_active_row`):** When $n = d$, the matrix $v \in \mathbb{R}^{d \times d}$ of frame points has $\det(v) \neq 0$, and the Cramer linear functional `frameNormal v` with coefficients $\det(v.\mathrm{updateCol}\;k\;\mathbf{1}) / \det(v)$ equals an actual defining facet row $L_j$ active at $p$ without any additional oracle query.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed., Graduate Texts in Mathematics 221), §3.6, pp. 52b–52c (citing Gritzmann–Klee–Westwater 1995)

import Definitions.Def_Grunbaum2003_IsPolytopeRayOracle
import Definitions.Def_Grunbaum2003_IsDPolytope
import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
open scoped BigOperators Matrix

namespace Grunbaum2003

theorem rayFrame_boundary_extension_axes_and_cramer_normal :
    ∃ (coordinateAxis : ∀ {d : ℕ}, Fin d → Fin d → ℝ)
      (frameCramerCoefficients : ∀ {d : ℕ}, Matrix (Fin d) (Fin d) ℝ → Fin d → ℝ)
      (frameNormal : ∀ {d : ℕ}, Matrix (Fin d) (Fin d) ℝ → (Fin d → ℝ) →L[ℝ] ℝ),
      (∀ (d : ℕ) (i : Fin d), coordinateAxis i = Pi.single i 1) ∧
      (∀ (d : ℕ) (v : Matrix (Fin d) (Fin d) ℝ) (k : Fin d),
        frameCramerCoefficients v k = (v.updateCol k (fun _ => 1)).det / v.det) ∧
      (∀ (d : ℕ) (v : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ),
        frameNormal v x = ∑ k, frameCramerCoefficients v k * x k) ∧
      (∀ {d n m : ℕ} (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) {P : Set (Fin d → ℝ)},
        P = {x | ∀ j, L j x ≤ 1} →
        ∀ {oracle : (Fin d → ℝ) → (Fin d → ℝ)}, IsPolytopeRayOracle P oracle →
        ∀ (f : (Fin n → ℝ) →L[ℝ] (Fin d → ℝ)) (g : (Fin d → ℝ) →L[ℝ] (Fin n → ℝ)),
          Function.LeftInverse g f →
          IsPolytopeRayOracle (f ⁻¹' P) (fun r => g (oracle (f r))) ∧
            (∀ r, r ≠ 0 → f (g (oracle (f r))) = oracle (f r))) ∧
      (∀ {d n : ℕ} (v : Fin n → Fin d → ℝ),
        LinearIndependent ℝ v → n < d →
        ∃ i : Fin d, coordinateAxis i ∉ Submodule.span ℝ (Set.range v)) ∧
      (∀ {d : ℕ} (W : Submodule ℝ (Fin d → ℝ)) (p : Fin d → ℝ),
        p ∈ W → p ≠ 0 → ∀ (i : Fin d), coordinateAxis i ∉ W →
        ∃ j : Fin d, j ≠ i ∧ p j ≠ 0) ∧
      (∀ {d n m : ℕ} (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) {P : Set (Fin d → ℝ)},
        P = {x | ∀ j, L j x ≤ 1} →
        ∀ (v : Fin n → Fin d → ℝ), LinearIndependent ℝ v →
        ∀ (w : Fin n → ℝ), (∀ i, 0 < w i) → (∑ i, w i = 1) →
        (∀ i, v i ∈ P) →
        ∀ (p q : Fin d → ℝ), p ∈ P → q ∈ P →
        p = ∑ i, w i • v i →
        q ∉ Submodule.span ℝ (Set.range v) →
        ∀ (j : Fin m), L j p = 1 → L j q = 1 →
        let V : Fin (n + 1) → Fin d → ℝ := Fin.cons q v
        let W : Fin (n + 1) → ℝ := Fin.cons (1 / 2 : ℝ) (fun i => w i / 2)
        let p' := (1 / 2 : ℝ) • (p + q)
        LinearIndependent ℝ V ∧ (∀ i, 0 < W i) ∧ (∑ i, W i = 1) ∧
          p' = ∑ i, W i • V i ∧ (∀ i, V i ∈ P) ∧ p' ∈ frontier P ∧
          (∀ k : Fin m, L k p' = 1 → ∀ i, L k (V i) = 1)) ∧
      (∀ {d m : ℕ} (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) {P : Set (Fin d → ℝ)},
        P = {x | ∀ j, L j x ≤ 1} →
        ∀ (v : Matrix (Fin d) (Fin d) ℝ), LinearIndependent ℝ v →
        ∀ (w : Fin d → ℝ), (∀ i, 0 < w i) → (∑ i, w i = 1) →
        (∀ i, v i ∈ P) →
        ∀ (p : Fin d → ℝ), p ∈ frontier P → p = ∑ i, w i • v i →
        v.det ≠ 0 ∧ ∃ j : Fin m, frameNormal v = L j ∧ L j p = 1) := by sorry

end Grunbaum2003
