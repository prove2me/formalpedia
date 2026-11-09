-- Prove2me | Theorems.Thm_Grunbaum2003_improving_edge_and_global_facet_from_ridge_pairs
-- name    : Grunbaum2003.improving_edge_and_global_facet_from_ridge_pairs
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-08T22:02:11.576618+00:00
-- url     : https://prove2.me/theorems/326a1f6e-89f7-4c6b-a32a-7368cb6bcc2e
-- title:
--   Improving-edge lemma and global facet synthesis via two-pass edge closure
-- statement:
--   1. (**Improving-edge lemma for exposed faces of polytopes**) Let $P \subseteq \mathbb{R}^n$ be a $d$-polytope, let $K$ be an exposed face of $P$, let $a \in K$ be an exposed vertex of $P$, and let $\ell$ be a continuous linear functional such that $\ell(a) < \ell(x)$ for some $x \in K$. Then there exist an exposed $1$-face (edge) $E \le K$ of $P$ and an exposed vertex $b$ of $P$ such that $a, b \in E$ and $\ell(a) < \ell(b)$.
--
--   2. (**Global facet synthesis from compatible local facets and two-ridge gluing**) Let $d \ge 3$, let $P, Q \subseteq \mathbb{R}^{d+1}$ be $(d+1)$-polytopes, let $\varphi : \operatorname{skel}_{d-1}(P) \xrightarrow{\sim} \operatorname{skel}_{d-1}(Q)$ be an order isomorphism of their $(d-1)$-skeleta, and let $F$ be a facet of $P$. Suppose that every exposed vertex $v \in F$ admits a compatible local facet $G_v$ of $Q$, any two compatible local facets at vertices sharing two distinct ridges of $F$ coincide, every exposed edge $E \le F$ lies in two distinct maximal elements $R_1 \ne R_2$ of $\operatorname{skel}_{d-1}(P)$ below $F$, and every maximal element of $\operatorname{skel}_{d-1}(Q)$ is a ridge of $Q$ (dimension $d - 1$). Then there exists a single facet $G$ of $Q$ such that
--
--   $$\forall S \in \operatorname{skel}_{d-1}(P), \qquad \varphi(S) \subseteq G \iff S \subseteq F.$$
--
--   **Formalization Note** Polytopes are represented by `IsDPolytope`, exposed faces by `PolytopeFace`, and the $(d-1)$-skeleton by `SkeletonFace P (d + 1 - 2)`.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer GTM 221, 2003), §12.3, Theorem 12.3.1, printed p. 228 / PDF p. 270; Xavier Allamigeon, Ricardo D. Katz, and Pierre-Yves Strub, Formalizing the Face Lattice of Polyhedra, Logical Methods in Computer Science 15(3), 2019, §5.1

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_SkeletonFace
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

set_option autoImplicit false

namespace Grunbaum2003

theorem improving_edge_and_global_facet_from_ridge_pairs :
    (∀ {n : ℕ} {P : Set (Fin n → ℝ)}, IsDPolytope P →
      ∀ (K : PolytopeFace P) (a : Fin n → ℝ), IsExposed ℝ P {a} → a ∈ K.val →
        ∀ (l : StrongDual ℝ (Fin n → ℝ)), (∃ x ∈ K.val, l a < l x) →
          ∃ (E : PolytopeFace P) (b : Fin n → ℝ),
            E.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ E.val).direction = 1 ∧
            E ≤ K ∧ IsExposed ℝ P {b} ∧ a ∈ E.val ∧ b ∈ E.val ∧ l a < l b) ∧
    (∀ (d : ℕ), 3 ≤ d →
      ∀ (P Q : Set (Fin (d + 1) → ℝ)), IsDPolytope P → IsDPolytope Q →
        ∀ (φ : SkeletonFace P (d + 1 - 2) ≃o SkeletonFace Q (d + 1 - 2))
          (F : PolytopeFace P),
          (F.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ F.val).direction = d) →
          (∀ (v : Fin (d + 1) → ℝ), IsExposed ℝ P {v} → v ∈ F.val →
            ∃ G : PolytopeFace Q,
              G.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ G.val).direction = d ∧
              (∀ S : SkeletonFace P (d + 1 - 2), v ∈ S.val.val → ((φ S).val ≤ G ↔ S.val ≤ F))) →
          (∀ (u w : Fin (d + 1) → ℝ) (G_u G_w : PolytopeFace Q),
            (G_u.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ G_u.val).direction = d) →
            (G_w.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ G_w.val).direction = d) →
            (∀ S : SkeletonFace P (d + 1 - 2), u ∈ S.val.val → ((φ S).val ≤ G_u ↔ S.val ≤ F)) →
            (∀ S : SkeletonFace P (d + 1 - 2), w ∈ S.val.val → ((φ S).val ≤ G_w ↔ S.val ≤ F)) →
            ∀ R₁ R₂ : SkeletonFace P (d + 1 - 2),
              R₁.val ≤ F → R₂.val ≤ F →
              u ∈ R₁.val.val → w ∈ R₁.val.val →
              u ∈ R₂.val.val → w ∈ R₂.val.val →
              ((φ R₁).val.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ (φ R₁).val.val).direction = d - 1) →
              ((φ R₂).val.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ (φ R₂).val.val).direction = d - 1) →
              R₁ ≠ R₂ →
              G_u = G_w) →
          (∀ (E : PolytopeFace P),
            (E.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ E.val).direction = 1) →
            E ≤ F →
            ∃ R₁ R₂ : SkeletonFace P (d + 1 - 2),
              R₁ ≠ R₂ ∧ R₁.val ≤ F ∧ R₂.val ≤ F ∧ E ≤ R₁.val ∧ E ≤ R₂.val ∧
              (∀ T : SkeletonFace P (d + 1 - 2), R₁ ≤ T → T = R₁) ∧
              (∀ T : SkeletonFace P (d + 1 - 2), R₂ ≤ T → T = R₂)) →
          (∀ (T : SkeletonFace Q (d + 1 - 2)),
            (∀ U : SkeletonFace Q (d + 1 - 2), T ≤ U → U = T) →
            T.val.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ T.val.val).direction = d - 1) →
          ∃ G : PolytopeFace Q,
            G.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ G.val).direction = d ∧
            (∀ S : SkeletonFace P (d + 1 - 2), (φ S).val ≤ G ↔ S.val ≤ F)) := by sorry

end Grunbaum2003
