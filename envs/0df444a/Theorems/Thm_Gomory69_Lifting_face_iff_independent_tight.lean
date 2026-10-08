-- Prove2me | Theorems.Thm_Gomory69_Lifting_face_iff_independent_tight
-- name    : Gomory69.Lifting.face_iff_independent_tight
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:01:00.729197+00:00
-- url     : https://prove2.me/theorems/f43916c0-19a2-4698-b190-3bab08d489f0
-- title:
--   p. 469, proof of THEOREM 7 — for π₀ > 0, a face is a valid inequality with n′ linearly independent tight points of T
-- statement:
--   Let $\mathcal G$ be a finite nontrivial Abelian group, $g_0\in\mathcal G$, $T=T(\mathcal G,g_0)$ the nonzero nonnegative integer solutions of the group equation, and $n'=|\mathcal G^+|=|\mathcal G|-1$. Let $\pi\in\mathbb R^{\mathcal G^+}$ and $\pi_0>0$. Then $(\pi,\pi_0)$ is a face of the master polyhedron $P(\mathcal G,g_0)$ if and only if
--
--   $$\pi\cdot t\ge\pi_0\ \text{ for all } t\in T,\qquad\text{and there are } t^1,\dots,t^{n'}\in T \text{ with } \pi\cdot t^i=\pi_0 \text{ that are linearly independent.}$$
--
--   The criterion turns the affine condition "the tight points generate the hyperplane" into a rank condition. It is the step that makes a count of independent minimal paths prove that an inequality is a face, and it is how THEOREM 19 is established.
--
--   **Formalization Note** This is THEOREM 7 of p. 469 with "basic feasible solution of $\{\pi t\ge\pi_0,\ t\in T\}$" unfolded: rows of rank $n'$ satisfied with equality are $n'$ linearly independent tight $t$. It is stated for the master polyhedron ($\mathcal N=\mathcal G^+$), the case this mission needs; the page states it for any $\mathcal N\subseteq\mathcal G^+$. The hypothesis $\pi_0>0$ is THEOREM 7's. Nontriviality makes the ambient T-space have positive dimension, as the paper's facet convention requires.
-- source:
--   Gomory, Some polyhedra related to combinatorial problems, Linear Algebra Appl. 2 (1969), pp. 469–470, THEOREM 7 and its proof

import Mathlib
import Definitions.Def_Gomory69_Lifting_GroupPolyhedron

namespace Gomory69.Lifting

theorem face_iff_independent_tight {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    [Nontrivial G]
    (g₀ : G) (π : Plus G → ℝ) (π₀ : ℝ) (hπ₀ : 0 < π₀) :
    IsFace G g₀ π π₀ ↔
      (∀ t ∈ T G g₀, π₀ ≤ π ⬝ᵥ castVec t) ∧
        ∃ s : Fin (Fintype.card (Plus G)) → (Plus G → ℕ),
          (∀ i, s i ∈ T G g₀ ∧ π ⬝ᵥ castVec (s i) = π₀) ∧
            LinearIndependent ℝ (fun i => castVec (s i)) := by sorry

end Gomory69.Lifting
