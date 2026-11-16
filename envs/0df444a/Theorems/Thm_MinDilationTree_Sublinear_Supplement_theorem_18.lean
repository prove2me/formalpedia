-- Prove2me | Theorems.Thm_MinDilationTree_Sublinear_Supplement_theorem_18
-- name    : MinDilationTree.Sublinear.Supplement.theorem_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T14:58:52.584105+00:00
-- url     : https://prove2.me/theorems/0b1f9009-0b40-49a4-8ac0-7cf7acb2477d
-- title:
--   Theorem 18 (Comb obstruction) — disconnected relevant vertices of $G_{F,\mathfrak S}$ force $\mathrm{Opt}\ge\Lambda/100$
-- statement:
--   Let $S$ be a set of $n$ distinct points in the plane, $D$ a Delaunay triangulation of $S$, and $\Lambda\ge6$ such that $S$ is $\Lambda$-thin. Let $r\ge0$, $P\in\mathcal P_r$, let $(\mathcal J,\mathcal F)$ be a junction tree of $P$, that is, a $(18\Lambda r,\ \tfrac23\Lambda^2r,\ (54\Lambda^2\log_2 n)\,r)$-junction tree, let $F\in\mathcal F$ be a face and let $\mathfrak S\subseteq\operatorname{spines}(F)$ be a set of $F$-spines. If the relevant vertices of the spine-cutting graph $G_{F,\mathfrak S}$ (with buffer radius $z_1=4r$) do not all lie in one connected component of $G_{F,\mathfrak S}$, then
--   $$\mathrm{Opt}\ \ge\ \frac{1}{100}\,\Lambda.$$
--
--   This is the second obstruction, a generalization of the comb lower bound of §3. Lemma 23 uses it to certify the lower bound whenever a good cut cannot be built.
--
--   Differences from the source:
--   - reading: the Delaunay triangulation of S → every Delaunay triangulation D of S (an inclusion-maximal plane graph of empty-disk edges); the r-support and Λ-thinness are taken w.r.t. that D; reason: reading R1: the paper assumes no general position; in general position D is unique
--   - reading: the junction tree of P (Definition 13: the one built by Lemma 12) → every (18Λr, (2/3)Λ²r, (54Λ² log₂ n)r)-junction tree of P in the sense of Definition 11; reason: reading R2: the proof uses only the properties of Definition 11 with these parameters; log = log₂ (reading R4)
--   - reading: Definition 11: J ∪ F a partition (footnote 4) whose intersection graph is a tree; no two junctions (faces) share a boundary; geodesic diameters of junctions ≤ α and of faces ≤ γ; geodesic distance between junctions ≥ β → pieces are weakly simple walks; their regions cover P and for every ε > 0 their vertices can be moved by < ε inside P to pairwise disjoint weakly simple polygons; distinct junctions are disjoint, distinct faces are disjoint; diameters are measured by the geodesic distance inside the piece, the junction separation by d_P; reason: pieces of a partition meet only along their boundaries, so two of them share a boundary exactly when they intersect; 'the vertices can be ε-perturbed within P' is read as perturbed vertices lying in P
--   - reading: weakly simple polygon: (i) for every ε > 0 its vertices can be ε-perturbed to a simple polygon, (ii) its complement is path-connected; repeated visits are distinct vertices → a closed boundary walk whose ordered subdivision can be ε-perturbed to a simple polygon for every ε > 0, and whose closed region (the trace plus the points the walk winds around an odd number of times) has a path-connected complement; reason: the paper explicitly admits singletons and doubly traversed segments (p. 3, Figure 1), which have fewer than three vertices and cannot be perturbed vertex for vertex; subdividing an edge changes no polygon, and a walk perturbable as given uses the trivial subdivision
--   - reading: Definitions 14–17 (spines, nerves, buffer, spine-cutting graph, relevant vertices) → F-spines/F-nerves: connected components of P_{r/Λ} ∩ F and P_{r/Λ²} ∩ F; z-buffer: points of F within d_P-distance z of a junction meeting F; an edge of G_{F,𝔖} joins two vertex regions when a path from a point of one to a point of the other has image in F \ B_{4r}(F), meets at most one spine of 𝔖 and no F-nerve contained in a spine of 𝔖; int(F) = region minus the boundary walk; reason: the buffer uses d_P as in the proof of Theorem 18 (p. 13); the outer-face vertex is kept distinct from component vertices whose region overlaps it
--   - encoding: P ∈ P_r → 0 ≤ r and P ∈ support p D r; reason: Definition 2 defines P_r for r ≥ 0 only
--   - encoding: Opt and the bound as real numbers; the points as a set S → Opt and the bound in ℝ≥0∞ (the published opt of the live mission); S as an injective map Fin n → ℝ²; reason: finite trees on distinct points have finite dilation, so the values are unchanged
-- source:
--   Sarita de Berg, Jacobus Conradi, Peter Kramer, André Nusser, Sampson Wong, STOC 2027 submission #185 (October 2026), p. 12 (PDF p. 13), Theorem 18; proof pp. 12–15 (PDF pp. 13–16)

import Mathlib
import Definitions.Def_MinDilationTree_Sublinear_Supplement_SpineCut

open scoped ENNReal

set_option autoImplicit false

namespace MinDilationTree.Sublinear.Supplement

open MinDilationTree.Sublinear

/-- Theorem 18 (Comb obstruction), p.12 (PDF 13). Let `S` be `Λ`-thin (w.r.t. a Delaunay
triangulation `D`) with `Λ ≥ 6`, let `F` be a face of a junction tree of `P ∈ P_r` (Definition 13,
reading R2), and let `𝔖 ⊆ spines(F)`. If the relevant vertices of `G_{F,𝔖}` are not in a single
connected component of `G_{F,𝔖}`, then `Opt ≥ Λ/100`. -/
theorem theorem_18 {n : ℕ} (p : Fin n → Plane) (hp : Function.Injective p)
    (D : SimpleGraph (Fin n)) (hD : IsDelaunay p D)
    (Λ : ℝ) (hΛ : 6 ≤ Λ) (hthin : PointSetThin p D Λ)
    (r : ℝ) (hr : 0 ≤ r) (P : Set Plane) (hP : P ∈ support p D r)
    (Q : JunctionTreeData) (hQ : IsTheJunctionTree n Λ r P Q)
    (F : BoundaryWalk) (hF : F ∈ Q.faces)
    (𝔖 : Set (Set Plane)) (h𝔖 : 𝔖 ⊆ fSpines p D Λ r F.region)
    (hsplit : ¬ ∀ u v : CutVertex F 𝔖, Relevant Q F 𝔖 u → Relevant Q F 𝔖 v →
      (spineCuttingGraph p D Λ r P Q F 𝔖).Reachable u v) :
    ENNReal.ofReal (Λ / 100) ≤ opt p := by sorry

end MinDilationTree.Sublinear.Supplement
