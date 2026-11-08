-- Prove2me | Theorems.Thm_Grunbaum2003_vertex_figure_induced_skeleton_iso_and_upper_interval_lift
-- name    : Grunbaum2003.vertex_figure_induced_skeleton_iso_and_upper_interval_lift
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-08T02:33:54.157649+00:00
-- url     : https://prove2.me/theorems/72fe57c4-e2d5-49da-b3ef-5fdfa8da38e9
-- title:
--   Induced vertex-figure skeleton order isomorphism, facet dimension shift, and upper-interval down-set lifting
-- statement:
--   This theorem establishes the inductive step mechanism on vertex figures in Grünbaum's Theorem 12.3.1:
--   1. **Facet of a Vertex Figure (`vertex_figure_facet_of_facet_containing_v`):** For $d \ge 2$, any facet $F$ of $P$ (direction finrank $d - 1$) containing $v$ is strictly larger than $\{v\}$ and maps under $\Psi_P : \{G \in \operatorname{PolytopeFace} P \mid v \in G\} \xrightarrow{\sim} \operatorname{PolytopeFace} Q_0$ to a facet $\Psi_P\langle F, hvF\rangle$ of the $(d-1)$-polytope $Q_0$ (nonempty and of direction finrank $d - 2$).
--   2. **Induced Vertex-Figure Skeleton Isomorphism and Upper-Interval Down-Set Lift (`induced_vertex_figure_skeletonIso`, `lift_vertex_figure_downSet_to_upper_interval`):** Any skeleton order isomorphism $\varphi : \operatorname{SkeletonFace} P (k+1) \xrightarrow{\sim} \operatorname{SkeletonFace} Q (l+1)$ sending $\{v\}$ to $\{v'\}$ restricts to the upper intervals of faces containing $v$ and $v'$ and conjugates via $\Psi_{\mathrm{skel}, P}$ and $\Psi_{\mathrm{skel}, Q}$ to an induced skeleton order isomorphism $\varphi_v : \operatorname{SkeletonFace} P_v k \xrightarrow{\sim} \operatorname{SkeletonFace} Q_{v'} l$. Moreover, if $G_{v'} \in \operatorname{PolytopeFace} Q_{v'}$ realizes the $\varphi_v$-down-set of $\Psi_P\langle F, hvF\rangle$, then $G = (\Psi_Q^{-1}(G_{v'})).\mathrm{val} \in \operatorname{PolytopeFace} Q$ contains $v'$ and satisfies $(\varphi S).\mathrm{val} \le G \iff S.\mathrm{val} \le F$ for every $S \in \operatorname{SkeletonFace} P (k+1)$ containing $v$.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed., Graduate Texts in Mathematics 221), §12.3, pp. 228–231, Theorem 12.3.1

import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_SkeletonFace
import Mathlib.Analysis.Convex.Exposed
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

set_option autoImplicit false

namespace Grunbaum2003

theorem vertex_figure_induced_skeleton_iso_and_upper_interval_lift :
  (∀ {d : ℕ} (hd : 2 ≤ d)
    {P : Set (Fin d → ℝ)} {Q₀ : Set (Fin (d - 1) → ℝ)} {v : Fin d → ℝ}
    (Ψ : {G : PolytopeFace P // v ∈ G.val} ≃o PolytopeFace Q₀),
    (∀ G : {G : PolytopeFace P // v ∈ G.val},
      G.val.val ≠ {v} →
        (Ψ G).val.Nonempty ∧
          Module.finrank ℝ (affineSpan ℝ G.val.val).direction =
            Module.finrank ℝ (affineSpan ℝ (Ψ G).val).direction + 1) →
    ∀ (F : PolytopeFace P),
      (F.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ F.val).direction = d - 1) →
      ∀ (hvF : v ∈ F.val),
        (Ψ ⟨F, hvF⟩).val.Nonempty ∧
          Module.finrank ℝ (affineSpan ℝ (Ψ ⟨F, hvF⟩).val).direction = d - 2) ∧
  (∀ {d : ℕ} (hd : 3 ≤ d)
    {R : Set (Fin d → ℝ)} {Q₀ : Set (Fin (d - 1) → ℝ)} {v : Fin d → ℝ}
    (Ψ : {G : PolytopeFace R // v ∈ G.val} ≃o PolytopeFace Q₀),
    (∀ k : ℕ,
      ∃ Ψ_skel : {S : SkeletonFace R (k + 1) // v ∈ S.val.val} ≃o
          SkeletonFace Q₀ k,
        ∀ S : {S : SkeletonFace R (k + 1) // v ∈ S.val.val},
          (Ψ_skel S).val = Ψ ⟨S.val.val, S.property⟩) →
    ∃ Ψ_skel : {S : SkeletonFace R (d - 2) // v ∈ S.val.val} ≃o
        SkeletonFace Q₀ (d - 3),
      ∀ S : {S : SkeletonFace R (d - 2) // v ∈ S.val.val},
        (Ψ_skel S).val = Ψ ⟨S.val.val, S.property⟩) ∧
  (∀ {d e d' e' K L k l : ℕ}
    {P : Set (Fin d → ℝ)} {Q : Set (Fin e → ℝ)}
    {P_v : Set (Fin d' → ℝ)} {Q_v' : Set (Fin e' → ℝ)}
    (vertexSkeletonFace : ∀ {m : ℕ} (R : Set (Fin m → ℝ)) (r : ℕ)
      (x : Fin m → ℝ), IsExposed ℝ R {x} → SkeletonFace R r)
    (hVertexVal : ∀ {m : ℕ} (R : Set (Fin m → ℝ)) (r : ℕ)
      (x : Fin m → ℝ) (hx : IsExposed ℝ R {x}),
      (vertexSkeletonFace R r x hx).val.val = {x})
    (φ : SkeletonFace P K ≃o SkeletonFace Q L)
    (v : Fin d → ℝ) (hv : IsExposed ℝ P {v})
    (v' : Fin e → ℝ) (hv' : IsExposed ℝ Q {v'})
    (hφv : φ (vertexSkeletonFace P K v hv) = vertexSkeletonFace Q L v' hv')
    (Ψ_P : {G : PolytopeFace P // v ∈ G.val} ≃o PolytopeFace P_v)
    (Ψ_Q : {H : PolytopeFace Q // v' ∈ H.val} ≃o PolytopeFace Q_v')
    (Ψ_skel_P : {S : SkeletonFace P K // v ∈ S.val.val} ≃o SkeletonFace P_v k)
    (hΨ_skel_P : ∀ S : {S : SkeletonFace P K // v ∈ S.val.val},
      (Ψ_skel_P S).val = Ψ_P ⟨S.val.val, S.property⟩)
    (Ψ_skel_Q : {T : SkeletonFace Q L // v' ∈ T.val.val} ≃o SkeletonFace Q_v' l)
    (hΨ_skel_Q : ∀ T : {T : SkeletonFace Q L // v' ∈ T.val.val},
      (Ψ_skel_Q T).val = Ψ_Q ⟨T.val.val, T.property⟩),
    ∃ φ_v : SkeletonFace P_v k ≃o SkeletonFace Q_v' l,
      ∀ (F : PolytopeFace P) (hvF : v ∈ F.val) (G_v' : PolytopeFace Q_v'),
        (∀ T₀ : SkeletonFace Q_v' l,
          T₀.val ≤ G_v' ↔ (φ_v.symm T₀).val ≤ Ψ_P ⟨F, hvF⟩) →
        let G : PolytopeFace Q := (Ψ_Q.symm G_v').val
        v' ∈ G.val ∧
        ∀ (S : SkeletonFace P K), v ∈ S.val.val →
          ((φ S).val ≤ G ↔ S.val ≤ F)) := by sorry

end Grunbaum2003
