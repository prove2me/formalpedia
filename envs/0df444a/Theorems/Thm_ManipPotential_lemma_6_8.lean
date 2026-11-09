-- Prove2me | Theorems.Thm_ManipPotential_lemma_6_8
-- name    : ManipPotential.lemma_6_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:45:01.114623+00:00
-- url     : https://prove2.me/theorems/5f290cc3-0c06-4f22-bebd-4b1579629893
-- title:
--   Lemma 6.8 — Sperner's lemma
-- statement:
--   Let $S = \mathrm{conv}\{p_0, \dots, p_d\}$ be a $d$-simplex in a real vector space, with $p_0, \dots, p_d$ affinely independent, and facet $j$ the face spanned by the vertices other than $p_j$. Let $\mathcal T$ be a triangulation of $S$ and let the vertices of $\mathcal T$ be labelled by $[d+1]$ so that no vertex on facet $j$ is labelled $j$ (a Sperner labelling). Then $\mathcal T$ contains an **odd** number of fully labelled elementary $d$-simplices; in particular, it contains at least one.
--
--   The paper cites this classical result [Su99, Section 2]; it is the combinatorial input for the existence of common junctions in Proposition 6.11.
--
--   Differences from the source:
--   - generalization: d ≥ 1 → every d ≥ 0; reason: at d = 0 the simplex is a point and the statement is immediate; it specializes to the source for d ≥ 1
--   - encoding: facets indexed by [d+1] in some fixed way → facet j is the face opposite the vertex p_j; reason: any bijection of facets with labels is obtained by renumbering the vertices
--   - encoding: triangulation as a finite collection of d-simplices meeting in common faces → a finite geometric simplicial complex with underlying space S in which every face lies in a face with d + 1 vertices; labels as a function on the ambient space read on the vertices; reason: Lean convention; same triangulations and labellings
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Lemma 6.8, p.31

import Mathlib
import Definitions.Def_ManipPotential_IsTriangulationOf
import Definitions.Def_ManipPotential_IsSpernerLabelling
import Definitions.Def_ManipPotential_IsFullyLabelled

namespace ManipPotential

/-- Sperner's lemma (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Lemma 6.8, p.31, citing Su 1999, Section 2): every Sperner-labelled
triangulation of a `d`-simplex contains an odd number of fully labelled elementary `d`-simplices; in
particular, there is at least one. -/
theorem lemma_6_8 {E : Type*} [AddCommGroup E] [Module ℝ E] (d : ℕ) (p : Fin (d + 1) → E)
    (hp : AffineIndependent ℝ p) (K : Geometry.SimplicialComplex ℝ E)
    (hK : IsTriangulationOf K d p) (lab : E → Fin (d + 1)) (hlab : IsSpernerLabelling K p lab) :
    Odd {s | s ∈ K.faces ∧ IsFullyLabelled lab s}.ncard ∧
      ∃ s ∈ K.faces, IsFullyLabelled lab s := by sorry

end ManipPotential
