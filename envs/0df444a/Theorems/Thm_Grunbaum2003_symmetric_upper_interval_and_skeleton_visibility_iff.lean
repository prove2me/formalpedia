-- Prove2me | Theorems.Thm_Grunbaum2003_symmetric_upper_interval_and_skeleton_visibility_iff
-- name    : Grunbaum2003.symmetric_upper_interval_and_skeleton_visibility_iff
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-08T03:45:50.013195+00:00
-- url     : https://prove2.me/theorems/2ab50251-9506-4b76-b183-a2232e63ccce
-- title:
--   Symmetric upper-interval transfer under $\varphi^{-1}$, ridge-coatom gluing of local lifts, and full exposed-vertex equivalence
-- statement:
--   Suppose $\varphi : \operatorname{SkeletonFace} P K \xrightarrow{\sim} \operatorname{SkeletonFace} Q L$ maps $\{v\}$ to $\{v'\}$ and $G \in \operatorname{PolytopeFace} Q$ satisfies the upper-interval equivalence
--   $$
--   \forall S : \operatorname{SkeletonFace} P K,\quad v \in S.\mathrm{val}.\mathrm{val} \implies ((\varphi S).\mathrm{val} \le G \iff S.\mathrm{val} \le F).
--   $$
--   Then:
--   1. **Symmetric Upper-Interval Equivalence:** $\varphi^{-1}$ automatically satisfies $\forall T : \operatorname{SkeletonFace} Q L,\ v' \in T.\mathrm{val}.\mathrm{val} \implies ((\varphi.\mathrm{symm}\, T).\mathrm{val} \le F \iff T.\mathrm{val} \le G)$.
--   2. **Ridge-Coatom Gluing (`lifted_faces_eq_of_two_shared_ridges`):** If $G_u$ and $G_w$ satisfy the upper-interval equivalence at $u$ and $w$, and $R_1, R_2 \le F$ are two skeleton faces containing both $u$ and $w$ with $R_2 \not\le R_1$ such that $\varphi(R_1)$ is a maximal proper subface of both $G_u$ and $G_w$, then $G_u = G_w$ (via the exposed intersection $G_u \cap G_w$).
--   3. **Local Upper-Interval Visibility Equivalence:** If every exposed vertex $x \in F$ shares a skeleton face $E \le F$ with some vertex $u$ where $G$ satisfies the upper-interval equivalence, and symmetrically for every exposed vertex $y \in G$, then $(\varphi(\{x\})).\mathrm{val} \le G \iff x \in F.\mathrm{val}$ holds for all exposed vertices $x$ of $P$.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed., Graduate Texts in Mathematics 221), §12.3, pp. 228–231, Theorem 12.3.1

import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_SkeletonFace
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

set_option autoImplicit false

namespace Grunbaum2003

theorem symmetric_upper_interval_and_skeleton_visibility_iff :
  ∀ {d e K L : ℕ} {P : Set (Fin d → ℝ)} {Q : Set (Fin e → ℝ)},
    ({x : Fin d → ℝ | IsExposed ℝ P {x}}.Finite ∧
      ∀ E : PolytopeFace P,
        E.val = convexHull ℝ (E.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}})) →
    ({y : Fin e → ℝ | IsExposed ℝ Q {y}}.Finite ∧
      ∀ E : PolytopeFace Q,
        E.val = convexHull ℝ (E.val ∩ {y : Fin e → ℝ | IsExposed ℝ Q {y}})) →
    ∀ (vertexSkeletonFace : ∀ {m : ℕ} (R : Set (Fin m → ℝ)) (r : ℕ)
        (x : Fin m → ℝ), IsExposed ℝ R {x} → SkeletonFace R r)
      (hVertexVal : ∀ {m : ℕ} (R : Set (Fin m → ℝ)) (r : ℕ)
        (x : Fin m → ℝ) (hx : IsExposed ℝ R {x}),
        (vertexSkeletonFace R r x hx).val.val = {x})
      (φ : SkeletonFace P K ≃o SkeletonFace Q L)
      (v : Fin d → ℝ) (hv : IsExposed ℝ P {v})
      (v' : Fin e → ℝ) (hv' : IsExposed ℝ Q {v'})
      (hφv : φ (vertexSkeletonFace P K v hv) = vertexSkeletonFace Q L v' hv')
      (F : PolytopeFace P) (G : PolytopeFace Q)
      (hUpper : ∀ S : SkeletonFace P K, v ∈ S.val.val →
        ((φ S).val ≤ G ↔ S.val ≤ F)),
      (∀ T : SkeletonFace Q L, v' ∈ T.val.val →
        ((φ.symm T).val ≤ F ↔ T.val ≤ G)) ∧
      (∀ (u w : Fin d → ℝ) (G_u G_w : PolytopeFace Q),
        (∀ S : SkeletonFace P K, u ∈ S.val.val → ((φ S).val ≤ G_u ↔ S.val ≤ F)) →
        (∀ S : SkeletonFace P K, w ∈ S.val.val → ((φ S).val ≤ G_w ↔ S.val ≤ F)) →
        ∀ R₁ R₂ : SkeletonFace P K,
          R₁.val ≤ F → R₂.val ≤ F →
          u ∈ R₁.val.val → w ∈ R₁.val.val →
          u ∈ R₂.val.val → w ∈ R₂.val.val →
          ¬ (R₂.val ≤ R₁.val) →
          (∀ H : PolytopeFace Q, (φ R₁).val ≤ H → H ≤ G_u → H = (φ R₁).val ∨ H = G_u) →
          (∀ H : PolytopeFace Q, (φ R₁).val ≤ H → H ≤ G_w → H = (φ R₁).val ∨ H = G_w) →
          G_u = G_w ∧
          (∀ S : SkeletonFace P K, w ∈ S.val.val → ((φ S).val ≤ G_u ↔ S.val ≤ F))) ∧
      ((∀ (x : Fin d → ℝ), IsExposed ℝ P {x} →
          x ∈ F.val →
            ∃ (u : Fin d → ℝ) (E : SkeletonFace P K),
              (∀ S : SkeletonFace P K, u ∈ S.val.val → ((φ S).val ≤ G ↔ S.val ≤ F)) ∧
              E.val ≤ F ∧ u ∈ E.val.val ∧ x ∈ E.val.val) →
        (∀ (y : Fin e → ℝ), IsExposed ℝ Q {y} →
          y ∈ G.val →
            ∃ (u' : Fin e → ℝ) (E' : SkeletonFace Q L),
              (∀ T : SkeletonFace Q L, u' ∈ T.val.val → ((φ.symm T).val ≤ F ↔ T.val ≤ G)) ∧
              E'.val ≤ G ∧ u' ∈ E'.val.val ∧ y ∈ E'.val.val) →
        ∀ (x : Fin d → ℝ) (hx : IsExposed ℝ P {x}),
          ((φ (vertexSkeletonFace P K x hx)).val ≤ G ↔ x ∈ F.val)) := by sorry

end Grunbaum2003
