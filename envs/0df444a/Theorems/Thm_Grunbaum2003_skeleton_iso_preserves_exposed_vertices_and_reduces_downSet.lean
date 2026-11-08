-- Prove2me | Theorems.Thm_Grunbaum2003_skeleton_iso_preserves_exposed_vertices_and_reduces_downSet
-- name    : Grunbaum2003.skeleton_iso_preserves_exposed_vertices_and_reduces_downSet
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-08T01:30:19.452474+00:00
-- url     : https://prove2.me/theorems/dc12f5af-16f8-45c1-a7ee-2ab6fe37989b
-- title:
--   Order-theoretic preservation of exposed vertices and vertex-level reduction of skeleton down-set correspondence
-- statement:
--   Under the exposed-vertex hull representation $E = \operatorname{conv}(E \cap \operatorname{vert}(P))$ and $E = \operatorname{conv}(E \cap \operatorname{vert}(Q))$, every singleton exposed vertex $\{x\}$ belongs to the $k$-skeleton poset `SkeletonFace P k` (`vertexSkeletonFace P k x hx`), and any order isomorphism $\varphi : \operatorname{SkeletonFace} P k \xrightarrow{\sim} \operatorname{SkeletonFace} Q l$ satisfies:
--   1. **Empty-face invariance:** $(\varphi S).\mathrm{val}.\mathrm{val} = \emptyset \iff S.\mathrm{val}.\mathrm{val} = \emptyset$.
--   2. **Atom/vertex preservation (without any dimension-preservation hypothesis):** For every exposed vertex $x \in \operatorname{vert}(P)$, $\varphi(\{x\})$ is a singleton exposed vertex $\{y\}$ of $Q$ (`IsExposed ℝ Q {y}`).
--   3. **Vertex-level reduction of skeleton down-sets:** For any exposed faces $F \in \mathcal{F}(P)$ and $G \in \mathcal{F}(Q)$, the full skeleton principal down-set correspondence
--      $$
--      \forall T \in \operatorname{SkeletonFace} Q l,\quad T.\mathrm{val} \le G \iff (\varphi^{-1}(T)).\mathrm{val} \le F
--      $$
--      holds if and only if it holds on singleton exposed vertices:
--      $$
--      \forall x \in \operatorname{vert}(P),\quad \varphi(\{x\}).\mathrm{val} \le G \iff x \in F.\mathrm{val}.
--      $$
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

theorem skeleton_iso_preserves_exposed_vertices_and_reduces_downSet :
  ∃ (vertexSkeletonFace : ∀ {d : ℕ} (P : Set (Fin d → ℝ)) (k : ℕ)
      (x : Fin d → ℝ), IsExposed ℝ P {x} → SkeletonFace P k),
    (∀ {d : ℕ} (P : Set (Fin d → ℝ)) (k : ℕ) (x : Fin d → ℝ) (hx : IsExposed ℝ P {x}),
      (vertexSkeletonFace P k x hx).val.val = {x}) ∧
    (∀ {d e k l : ℕ} {P : Set (Fin d → ℝ)} {Q : Set (Fin e → ℝ)},
      (∀ E : PolytopeFace P,
        E.val = convexHull ℝ (E.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}})) →
      (∀ E : PolytopeFace Q,
        E.val = convexHull ℝ (E.val ∩ {y : Fin e → ℝ | IsExposed ℝ Q {y}})) →
      ∀ (φ : SkeletonFace P k ≃o SkeletonFace Q l),
      (∀ S : SkeletonFace P k, (φ S).val.val = ∅ ↔ S.val.val = ∅) ∧
      (∀ (x : Fin d → ℝ) (hx : IsExposed ℝ P {x}),
        ∃ (y : Fin e → ℝ) (hy : IsExposed ℝ Q {y}),
          φ (vertexSkeletonFace P k x hx) = vertexSkeletonFace Q l y hy) ∧
      (∀ (F : PolytopeFace P) (G : PolytopeFace Q),
        (∀ T : SkeletonFace Q l, T.val ≤ G ↔ (φ.symm T).val ≤ F) ↔
          (∀ (x : Fin d → ℝ) (hx : IsExposed ℝ P {x}),
            (φ (vertexSkeletonFace P k x hx)).val ≤ G ↔ x ∈ F.val))) := by sorry

end Grunbaum2003
