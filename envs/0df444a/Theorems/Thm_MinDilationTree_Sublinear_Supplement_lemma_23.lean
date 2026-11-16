-- Prove2me | Theorems.Thm_MinDilationTree_Sublinear_Supplement_lemma_23
-- name    : MinDilationTree.Sublinear.Supplement.lemma_23
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T14:59:52.211255+00:00
-- url     : https://prove2.me/theorems/44378608-3a19-4a4f-a88b-fd1abc4ad50b
-- title:
--   Lemma 23 — a good cut of $G_{F,\mathfrak S}$ or a certificate $\mathrm{Opt}\ge\Lambda/100$ in $O(n^2\log n)$ time
-- statement:
--   There is a single deterministic real-RAM algorithm with the following guarantee. Let $S$ be a set of $n$ distinct points in the plane, $D$ a Delaunay triangulation of $S$, and $\Lambda\ge6$ such that $S$ is $\Lambda$-thin. Let $r\ge0$, $P\in\mathcal P_r$, and let $(\mathcal J,\mathcal F)$ be a junction tree of $P$ (a $(18\Lambda r,\ \tfrac23\Lambda^2r,\ (54\Lambda^2\log_2 n)\,r)$-junction tree). Given a face $F\in\mathcal F$ and a set $\mathfrak S\subseteq\operatorname{spines}(F)$, the algorithm either
--
--   1. constructs a good cut $C$ of the spine-cutting graph $G_{F,\mathfrak S}$, or
--   2. certifies that $\mathrm{Opt}\ge\frac1{100}\Lambda$,
--
--   in $O(n^2\log n)$ time. Every cut it outputs is in midpoint form: each Delaunay triangle meets $C$ in at most two segments joining edge midpoints.
--
--   Theorem 29 calls this algorithm with $\mathfrak S=\operatorname{spines}(F)$ for every face, and the good cuts it returns drive the tree construction of §6.
--
--   **Formalization Note** A nonzero first output cell is the certificate, and it may appear only when $\mathrm{Opt}\ge\Lambda/100$; otherwise the output encodes a good cut. Correctness holds for every input. The time bound applies to inputs whose junction-tree encoding and spine list have length at most $Kn$: for every $K$ there are $C>0$ and $n_0\ge2$ with $t+1\le C\,n^2\log_2 n$ for $n\ge n_0$, uniformly in $\Lambda$ and $r$.
--
--   Differences from the source:
--   - reading: an algorithm with running time in O(f(n)), no machine model named → one admissible program of the published exact real RAM (rational literals, no random draws), with ∃ C > 0, ∃ n₀ ≥ 2 fixed with the program before every input (n, points, Λ, r, D and the other inputs), and t + 1 ≤ C·f(n) for n ≥ n₀; correctness for every n; reason: reading R0 of the live mission (the same model as its goal Theorem 1); the paper gives no explicit time constant; its bounds do not depend on Λ, so C is uniform in Λ
--   - reading: the Delaunay triangulation of S, computed by the algorithm → any Delaunay triangulation D (an inclusion-maximal plane graph of empty-disk edges) given as part of the input as an edge list over point labels; Λ-thinness, supports, spines and nerves all refer to that D; reason: reading R1: the paper assumes no general position, so every Delaunay triangulation is admitted; computing one takes O(n log n), within every time bound here, so supplying it changes no bound
--   - reading: the junction tree of P (Definition 13: the one built by Lemma 12) → every (18Λr, (2/3)Λ²r, (54Λ² log₂ n)r)-junction tree of P in the sense of Definition 11; reason: reading R2: the proof uses only the properties of Definition 11 with these parameters; log = log₂ (reading R4)
--   - reading: O(n² log n) time for the junction tree of P (the one of Lemma 12, of size O(n)) → for every K, constants C, n₀ such that the time bound holds whenever the input junction tree's encoding and the list of spine representatives have length at most K·n; reason: reading R2; the input junction tree is arbitrary, so its size must be bounded for an O(n² log n) bound to be meaningful, and the junction trees of Lemma 12 have linear size
--   - reading: Definition 11: J ∪ F a partition (footnote 4) whose intersection graph is a tree; no two junctions (faces) share a boundary; geodesic diameters of junctions ≤ α and of faces ≤ γ; geodesic distance between junctions ≥ β → pieces are weakly simple walks; their regions cover P and for every ε > 0 their vertices can be moved by < ε inside P to pairwise disjoint weakly simple polygons; distinct junctions are disjoint, distinct faces are disjoint; diameters are measured by the geodesic distance inside the piece, the junction separation by d_P; reason: pieces of a partition meet only along their boundaries, so two of them share a boundary exactly when they intersect; 'the vertices can be ε-perturbed within P' is read as perturbed vertices lying in P
--   - reading: weakly simple polygon: (i) for every ε > 0 its vertices can be ε-perturbed to a simple polygon, (ii) its complement is path-connected; repeated visits are distinct vertices → a closed boundary walk whose ordered subdivision can be ε-perturbed to a simple polygon for every ε > 0, and whose closed region (the trace plus the points the walk winds around an odd number of times) has a path-connected complement; reason: the paper explicitly admits singletons and doubly traversed segments (p. 3, Figure 1), which have fewer than three vertices and cannot be perturbed vertex for vertex; subdividing an edge changes no polygon, and a walk perturbable as given uses the trivial subdivision
--   - reading: Definitions 14–17 (spines, nerves, buffer, spine-cutting graph, relevant vertices) → F-spines/F-nerves: connected components of P_{r/Λ} ∩ F and P_{r/Λ²} ∩ F; z-buffer: points of F within d_P-distance z of a junction meeting F; an edge of G_{F,𝔖} joins two vertex regions when a path from a point of one to a point of the other has image in F \ B_{4r}(F), meets at most one spine of 𝔖 and no F-nerve contained in a spine of 𝔖; int(F) = region minus the boundary walk; reason: the buffer uses d_P as in the proof of Theorem 18 (p. 13); the outer-face vertex is kept distinct from component vertices whose region overlaps it
--   - encoding: P ∈ P_r → 0 ≤ r and P ∈ support p D r; reason: Definition 2 defines P_r for r ≥ 0 only
--   - encoding: inputs P, F, 𝔖 and outputs (junction trees, cuts, sequences) as abstract objects → P by the label of an input point in it; F by its index in the junction tree; 𝔖 by one representative point per spine; outputs as self-delimiting real lists (walks as coordinate lists, cuts as vertex coordinates plus an edge list, a nonzero first cell certifying the lower bound); reason: every polygon of P_r contains an input point and polygons of P_r are disjoint; spines are disjoint nonempty sets, so every subset of spines(F) has such a description; the decodings are unique
--   - generalization: a good cut of G_{F,𝔖} → a good cut of G_{F,𝔖} in midpoint form (vertices at midpoints of Delaunay edges, edges inside Delaunay triangles, at most two per triangle); reason: reading R3; the proof's construction (p. 42) produces this form and Lemma 25 uses it; dropping the clause gives the source's statement
-- source:
--   Sarita de Berg, Jacobus Conradi, Peter Kramer, André Nusser, Sampson Wong, STOC 2027 submission #185 (October 2026), p. 16 (PDF p. 17), Lemma 23; proof pp. 42–45 (PDF pp. 43–46)

import Mathlib
import Definitions.Def_MinDilationTree_Sublinear_Supplement_Encoding

open scoped ENNReal

set_option autoImplicit false

namespace MinDilationTree.Sublinear.Supplement

open MinDilationTree.Sublinear

/-- Lemma 23, p.16 (PDF 17). One admissible real-RAM program, given a `Λ`-thin point set with
`Λ ≥ 6`, a junction tree `(J, F)` of `P ∈ P_r` (Definition 13, reading R2), a face `F` and a set
`𝔖 ⊆ spines(F)`, either certifies `Opt ≥ Λ/100` (nonzero flag) or outputs a good cut of `G_{F,𝔖}`
(in midpoint form, reading R3), in `O(n² log n)` time for inputs of size `O(n)` (reading R2: for
every `K`, constants `C, n₀` after `K`). -/
theorem lemma_23 :
    ∃ A : MatMulTimeLP.Program, FewInnerTSP.Admissible A ∧
      (∀ (n : ℕ) (p : Fin n → Plane), Function.Injective p →
        ∀ D : SimpleGraph (Fin n), IsDelaunay p D →
        ∀ L : List (Fin n × Fin n), ListsGraph D L →
        ∀ Λ : ℝ, 6 ≤ Λ → PointSetThin p D Λ →
        ∀ r : ℝ, 0 ≤ r → ∀ i : Fin n, ∀ P ∈ support p D r, p i ∈ P →
        ∀ Q : JunctionTreeData, IsTheJunctionTree n Λ r P Q →
        ∀ f : Fin Q.faces.length, ∀ reps : List Plane,
          (∀ x ∈ reps, ∃ W ∈ fSpines p D Λ r (Q.faces.get f).region, x ∈ W) →
        ∀ ω : MatMulTimeLP.Tape,
          ∃ t : ℕ, MatMulTimeLP.HaltsAt A (lemma23Input p Λ r L i Q f reps) ω t ∧
            (outputFlag A (lemma23Input p Λ r L i Q f reps) ω t ≠ 0 →
              ENNReal.ofReal (Λ / 100) ≤ opt p) ∧
            (outputFlag A (lemma23Input p Λ r L i Q f reps) ω t = 0 →
              ∃ C : CutData,
                OutputIs A (lemma23Input p Λ r L i Q f reps) ω t ((0 : ℝ) :: encodeCut C) ∧
                GoodCut p D Λ r P Q (Q.faces.get f)
                  (spinesOf p D Λ r (Q.faces.get f).region reps) C ∧
                MidpointForm p D C)) ∧
      ∀ K : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
        ∀ (n : ℕ), n₀ ≤ n → ∀ (p : Fin n → Plane), Function.Injective p →
        ∀ D : SimpleGraph (Fin n), IsDelaunay p D →
        ∀ L : List (Fin n × Fin n), ListsGraph D L →
        ∀ Λ : ℝ, 6 ≤ Λ → PointSetThin p D Λ →
        ∀ r : ℝ, 0 ≤ r → ∀ i : Fin n, ∀ P ∈ support p D r, p i ∈ P →
        ∀ Q : JunctionTreeData, IsTheJunctionTree n Λ r P Q →
        (encodeJunctionTree Q).length ≤ K * n →
        ∀ f : Fin Q.faces.length, ∀ reps : List Plane,
          (∀ x ∈ reps, ∃ W ∈ fSpines p D Λ r (Q.faces.get f).region, x ∈ W) →
          reps.length ≤ K * n →
        ∀ ω : MatMulTimeLP.Tape, ∀ t : ℕ,
          MatMulTimeLP.HaltsAt A (lemma23Input p Λ r L i Q f reps) ω t →
            (t : ℝ) + 1 ≤ C * (n : ℝ) ^ 2 * log₂ n := by sorry

end MinDilationTree.Sublinear.Supplement
