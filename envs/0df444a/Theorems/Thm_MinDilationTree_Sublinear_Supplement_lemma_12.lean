-- Prove2me | Theorems.Thm_MinDilationTree_Sublinear_Supplement_lemma_12
-- name    : MinDilationTree.Sublinear.Supplement.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T14:59:26.696689+00:00
-- url     : https://prove2.me/theorems/6d015d52-5c80-4d9f-85ab-aeb51aa322d5
-- title:
--   Lemma 12 — a junction tree of a polygon of $\mathcal P_r$ in $O(n\log n)$ time
-- statement:
--   There is a single deterministic real-RAM algorithm with the following guarantee. Let $S$ be a set of $n$ distinct points in the plane, $D$ a Delaunay triangulation of $S$, and $\Lambda\ge6$ such that $S$ is $\Lambda$-thin. Given $S$, $\Lambda$, $r\ge0$, $D$ and a polygon $P$ of the $r$-support $\mathcal P_r(S)$, it computes an
--   $$\bigl(18\Lambda r,\ \tfrac23\Lambda^2 r,\ (54\Lambda^2\log_2 n)\,r\bigr)\text{-junction tree of }P$$
--   in $O(n\log n)$ time. Its output has size $O(n)$.
--
--   Theorem 29 calls this algorithm once for every polygon of every scale of a compressed scale sequence.
--
--   **Formalization Note** The program, a size constant $K_0$, a time constant $C>0$ and a threshold $n_0\ge2$ are fixed before the input; the output is correct for every $n$, its encoding has length at most $K_0n$, and the run takes $t+1\le C\,n\log_2 n$ steps for $n\ge n_0$. The paper gives no explicit time constant.
--
--   Differences from the source:
--   - reading: an algorithm with running time in O(f(n)), no machine model named → one admissible program of the published exact real RAM (rational literals, no random draws), with ∃ C > 0, ∃ n₀ ≥ 2 fixed with the program before every input (n, points, Λ, r, D and the other inputs), and t + 1 ≤ C·f(n) for n ≥ n₀; correctness for every n; reason: reading R0 of the live mission (the same model as its goal Theorem 1); the paper gives no explicit time constant; its bounds do not depend on Λ, so C is uniform in Λ
--   - reading: the Delaunay triangulation of S, computed by the algorithm → any Delaunay triangulation D (an inclusion-maximal plane graph of empty-disk edges) given as part of the input as an edge list over point labels; Λ-thinness, supports, spines and nerves all refer to that D; reason: reading R1: the paper assumes no general position, so every Delaunay triangulation is admitted; computing one takes O(n log n), within every time bound here, so supplying it changes no bound
--   - reading: the junction tree of P (Definition 13: the one built by Lemma 12) → every (18Λr, (2/3)Λ²r, (54Λ² log₂ n)r)-junction tree of P in the sense of Definition 11; reason: reading R2: the proof uses only the properties of Definition 11 with these parameters; log = log₂ (reading R4)
--   - reading: Definition 11: J ∪ F a partition (footnote 4) whose intersection graph is a tree; no two junctions (faces) share a boundary; geodesic diameters of junctions ≤ α and of faces ≤ γ; geodesic distance between junctions ≥ β → pieces are weakly simple walks; their regions cover P and for every ε > 0 their vertices can be moved by < ε inside P to pairwise disjoint weakly simple polygons; distinct junctions are disjoint, distinct faces are disjoint; diameters are measured by the geodesic distance inside the piece, the junction separation by d_P; reason: pieces of a partition meet only along their boundaries, so two of them share a boundary exactly when they intersect; 'the vertices can be ε-perturbed within P' is read as perturbed vertices lying in P
--   - reading: weakly simple polygon: (i) for every ε > 0 its vertices can be ε-perturbed to a simple polygon, (ii) its complement is path-connected; repeated visits are distinct vertices → a closed boundary walk whose ordered subdivision can be ε-perturbed to a simple polygon for every ε > 0, and whose closed region (the trace plus the points the walk winds around an odd number of times) has a path-connected complement; reason: the paper explicitly admits singletons and doubly traversed segments (p. 3, Figure 1), which have fewer than three vertices and cannot be perturbed vertex for vertex; subdividing an edge changes no polygon, and a walk perturbable as given uses the trivial subdivision
--   - encoding: P ∈ P_r → 0 ≤ r and P ∈ support p D r; reason: Definition 2 defines P_r for r ≥ 0 only
--   - encoding: inputs P, F, 𝔖 and outputs (junction trees, cuts, sequences) as abstract objects → P by the label of an input point in it; F by its index in the junction tree; 𝔖 by one representative point per spine; outputs as self-delimiting real lists (walks as coordinate lists, cuts as vertex coordinates plus an edge list, a nonzero first cell certifying the lower bound); reason: every polygon of P_r contains an input point and polygons of P_r are disjoint; spines are disjoint nonempty sets, so every subset of spines(F) has such a description; the decodings are unique
--   - generalization: a junction tree is computed (its size is not stated) → the output encoding has length at most K₀·n, with K₀ fixed with the program; reason: reading R2; the proof's partition has at most 2n − 1 pieces (Lemma 10) of linear total description, and dropping the clause gives the source's statement
-- source:
--   Sarita de Berg, Jacobus Conradi, Peter Kramer, André Nusser, Sampson Wong, STOC 2027 submission #185 (October 2026), p. 9 (PDF p. 10), Lemma 12; proof pp. 9–10 (PDF pp. 10–11)

import Mathlib
import Definitions.Def_MinDilationTree_Sublinear_Supplement_Encoding

open scoped ENNReal

set_option autoImplicit false

namespace MinDilationTree.Sublinear.Supplement

open MinDilationTree.Sublinear

/-- Lemma 12, p.9 (PDF 10). One admissible real-RAM program, given a `Λ`-thin point set with
`Λ ≥ 6` (w.r.t. the given Delaunay triangulation `D`), `r ≥ 0` and a polygon `P ∈ P_r`, outputs a
`(18Λr, (2/3)Λ²r, (54Λ² log n)r)`-junction tree of `P` (of encoding size at most `K₀·n`) in
`O(n log n)` time: `t + 1 ≤ C·n·log₂ n` for `n ≥ n₀`, with `K₀, C, n₀` fixed with the program. -/
theorem lemma_12 :
    ∃ A : MatMulTimeLP.Program, FewInnerTSP.Admissible A ∧ ∃ K₀ : ℕ,
      (∀ (n : ℕ) (p : Fin n → Plane), Function.Injective p →
        ∀ D : SimpleGraph (Fin n), IsDelaunay p D →
        ∀ L : List (Fin n × Fin n), ListsGraph D L →
        ∀ Λ : ℝ, 6 ≤ Λ → PointSetThin p D Λ →
        ∀ r : ℝ, 0 ≤ r → ∀ i : Fin n, ∀ ω : MatMulTimeLP.Tape,
          ∃ t : ℕ, MatMulTimeLP.HaltsAt A (lemma12Input p Λ r L i) ω t ∧
            ∃ Q : JunctionTreeData,
              OutputIs A (lemma12Input p Λ r L i) ω t (encodeJunctionTree Q) ∧
              (encodeJunctionTree Q).length ≤ K₀ * n ∧
              ∀ P ∈ support p D r, p i ∈ P → IsTheJunctionTree n Λ r P Q) ∧
      ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
        ∀ (n : ℕ), n₀ ≤ n → ∀ (p : Fin n → Plane), Function.Injective p →
        ∀ D : SimpleGraph (Fin n), IsDelaunay p D →
        ∀ L : List (Fin n × Fin n), ListsGraph D L →
        ∀ Λ : ℝ, 6 ≤ Λ → PointSetThin p D Λ →
        ∀ r : ℝ, 0 ≤ r → ∀ i : Fin n, ∀ ω : MatMulTimeLP.Tape, ∀ t : ℕ,
          MatMulTimeLP.HaltsAt A (lemma12Input p Λ r L i) ω t →
            (t : ℝ) + 1 ≤ C * (n : ℝ) * log₂ n := by sorry

end MinDilationTree.Sublinear.Supplement
