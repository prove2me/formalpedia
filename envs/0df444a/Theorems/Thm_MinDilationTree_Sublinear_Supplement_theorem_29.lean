-- Prove2me | Theorems.Thm_MinDilationTree_Sublinear_Supplement_theorem_29
-- name    : MinDilationTree.Sublinear.Supplement.theorem_29
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:02:46.250706+00:00
-- url     : https://prove2.me/theorems/3b33c46b-69ec-40b4-9c46-0b07abdbc843
-- title:
--   Theorem 29 — a consistent sequence of junction trees or a certificate $\mathrm{Opt}\ge\Lambda/100$ in $O(n^5\log n)$ time
-- statement:
--   There is a single deterministic real-RAM algorithm with the following guarantee. Let $S$ be a set of $n$ distinct points in the plane, $D$ a Delaunay triangulation of $S$, and $\Lambda\ge6$ such that $S$ is $\Lambda$-thin. Given $S$, $\Lambda$ and $D$, the algorithm either
--
--   1. computes a consistent sequence of junction trees for $S$: a compressed scale sequence $R$ and, for every $r\in R$, a junction tree $(\mathcal J_r,\mathcal F_r)$ of every polygon $P\in\mathcal P_r$, such that for every one of these junction trees and every face $F\in\mathcal F_r$ the spine-cutting graph $G_{F,\operatorname{spines}(F)}$ has a good cut; or
--   2. certifies that $\mathrm{Opt}\ge\frac1{100}\Lambda$,
--
--   in $O(n^5\log n)$ time.
--
--   This is the input of the tree construction of §6: given a consistent sequence, Algorithm 1 builds a tree of dilation $O(\max\{n/\Lambda,\Lambda^{14}\})$.
--
--   **Formalization Note** A nonzero first output cell is the certificate, allowed only when $\mathrm{Opt}\ge\Lambda/100$. Otherwise the output lists the scales, each with junction trees tagged by an input point of their polygon. The program, $C>0$ and $n_0\ge2$ are fixed before the input, correctness holds for every $n$, and $t+1\le C\,n^5\log_2 n$ for $n\ge n_0$, uniformly in $\Lambda$.
--
--   Differences from the source:
--   - reading: an algorithm with running time in O(f(n)), no machine model named → one admissible program of the published exact real RAM (rational literals, no random draws), with ∃ C > 0, ∃ n₀ ≥ 2 fixed with the program before every input (n, points, Λ, r, D and the other inputs), and t + 1 ≤ C·f(n) for n ≥ n₀; correctness for every n; reason: reading R0 of the live mission (the same model as its goal Theorem 1); the paper gives no explicit time constant; its bounds do not depend on Λ, so C is uniform in Λ
--   - reading: the Delaunay triangulation of S, computed by the algorithm → any Delaunay triangulation D (an inclusion-maximal plane graph of empty-disk edges) given as part of the input as an edge list over point labels; Λ-thinness, supports, spines and nerves all refer to that D; reason: reading R1: the paper assumes no general position, so every Delaunay triangulation is admitted; computing one takes O(n log n), within every time bound here, so supplying it changes no bound
--   - reading: the junction tree of P (Definition 13: the one built by Lemma 12) → every (18Λr, (2/3)Λ²r, (54Λ² log₂ n)r)-junction tree of P in the sense of Definition 11; reason: reading R2: the proof uses only the properties of Definition 11 with these parameters; log = log₂ (reading R4)
--   - reading: Definition 11: J ∪ F a partition (footnote 4) whose intersection graph is a tree; no two junctions (faces) share a boundary; geodesic diameters of junctions ≤ α and of faces ≤ γ; geodesic distance between junctions ≥ β → pieces are weakly simple walks; their regions cover P and for every ε > 0 their vertices can be moved by < ε inside P to pairwise disjoint weakly simple polygons; distinct junctions are disjoint, distinct faces are disjoint; diameters are measured by the geodesic distance inside the piece, the junction separation by d_P; reason: pieces of a partition meet only along their boundaries, so two of them share a boundary exactly when they intersect; 'the vertices can be ε-perturbed within P' is read as perturbed vertices lying in P
--   - reading: weakly simple polygon: (i) for every ε > 0 its vertices can be ε-perturbed to a simple polygon, (ii) its complement is path-connected; repeated visits are distinct vertices → a closed boundary walk whose ordered subdivision can be ε-perturbed to a simple polygon for every ε > 0, and whose closed region (the trace plus the points the walk winds around an odd number of times) has a path-connected complement; reason: the paper explicitly admits singletons and doubly traversed segments (p. 3, Figure 1), which have fewer than three vertices and cannot be perturbed vertex for vertex; subdividing an edge changes no polygon, and a walk perturbable as given uses the trivial subdivision
--   - reading: Definitions 14–17 (spines, nerves, buffer, spine-cutting graph, relevant vertices) → F-spines/F-nerves: connected components of P_{r/Λ} ∩ F and P_{r/Λ²} ∩ F; z-buffer: points of F within d_P-distance z of a junction meeting F; an edge of G_{F,𝔖} joins two vertex regions when a path from a point of one to a point of the other has image in F \ B_{4r}(F), meets at most one spine of 𝔖 and no F-nerve contained in a spine of 𝔖; int(F) = region minus the boundary walk; reason: the buffer uses d_P as in the proof of Theorem 18 (p. 13); the outer-face vertex is kept distinct from component vertices whose region overlaps it
--   - encoding: inputs P, F, 𝔖 and outputs (junction trees, cuts, sequences) as abstract objects → P by the label of an input point in it; F by its index in the junction tree; 𝔖 by one representative point per spine; outputs as self-delimiting real lists (walks as coordinate lists, cuts as vertex coordinates plus an edge list, a nonzero first cell certifying the lower bound); reason: every polygon of P_r contains an input point and polygons of P_r are disjoint; spines are disjoint nonempty sets, so every subset of spines(F) has such a description; the decodings are unique
-- source:
--   Sarita de Berg, Jacobus Conradi, Peter Kramer, André Nusser, Sampson Wong, STOC 2027 submission #185 (October 2026), p. 19 (PDF p. 20), Theorem 29 and Definition 28

import Mathlib
import Definitions.Def_MinDilationTree_Sublinear_Supplement_Encoding

open scoped ENNReal

set_option autoImplicit false

namespace MinDilationTree.Sublinear.Supplement

open MinDilationTree.Sublinear

/-- Theorem 29, p.19 (PDF 20). One admissible real-RAM program, given a `Λ`-thin set of `n` points
with `Λ ≥ 6` (w.r.t. the given Delaunay triangulation `D`), either certifies `Opt ≥ Λ/100` (nonzero
flag) or outputs a consistent sequence of junction trees (Definition 28), in `O(n⁵ log n)` time:
`t + 1 ≤ C·n⁵·log₂ n` for `n ≥ n₀`, with `C, n₀` fixed with the program (uniform in `Λ`). -/
theorem theorem_29 :
    ∃ A : MatMulTimeLP.Program, FewInnerTSP.Admissible A ∧
      (∀ (n : ℕ) (p : Fin n → Plane), Function.Injective p →
        ∀ D : SimpleGraph (Fin n), IsDelaunay p D →
        ∀ L : List (Fin n × Fin n), ListsGraph D L →
        ∀ Λ : ℝ, 6 ≤ Λ → PointSetThin p D Λ → ∀ ω : MatMulTimeLP.Tape,
          ∃ t : ℕ, MatMulTimeLP.HaltsAt A (theorem29Input p Λ L) ω t ∧
            (outputFlag A (theorem29Input p Λ L) ω t ≠ 0 →
              ENNReal.ofReal (Λ / 100) ≤ opt p) ∧
            (outputFlag A (theorem29Input p Λ L) ω t = 0 →
              ∃ scales : List (ℝ × List ScaleEntry),
                OutputIs A (theorem29Input p Λ L) ω t ((0 : ℝ) :: encodeScales scales) ∧
                IsConsistentSequence p D Λ scales)) ∧
      ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
        ∀ (n : ℕ), n₀ ≤ n → ∀ (p : Fin n → Plane), Function.Injective p →
        ∀ D : SimpleGraph (Fin n), IsDelaunay p D →
        ∀ L : List (Fin n × Fin n), ListsGraph D L →
        ∀ Λ : ℝ, 6 ≤ Λ → PointSetThin p D Λ → ∀ ω : MatMulTimeLP.Tape, ∀ t : ℕ,
          MatMulTimeLP.HaltsAt A (theorem29Input p Λ L) ω t →
            (t : ℝ) + 1 ≤ C * (n : ℝ) ^ 5 * log₂ n := by sorry

end MinDilationTree.Sublinear.Supplement
