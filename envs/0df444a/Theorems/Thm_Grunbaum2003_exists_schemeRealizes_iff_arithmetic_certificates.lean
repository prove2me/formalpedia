-- Prove2me | Theorems.Thm_Grunbaum2003_exists_schemeRealizes_iff_arithmetic_certificates
-- name    : Grunbaum2003.exists_schemeRealizes_iff_arithmetic_certificates
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-02T07:15:24.874085+00:00
-- url     : https://prove2.me/theorems/3f4d92aa-917b-4ed7-8e65-86dc89637ec3
-- title:
--   First-order real-field arithmetic characterization of vertex-face scheme realizability
-- statement:
--   This theorem reduces geometric realizability of a candidate vertex-face scheme $S$ on $k$ vertices in $\mathbb{R}^d$ (`∃ P : Set (Fin d → ℝ), SchemeRealizes k S P`) to an explicit first-order condition over the ordered real field $(\mathbb{R}, +, \cdot, <)$ in the vertex coordinates $V : \operatorname{Fin} k \to \mathbb{R}^d$ and linear support functionals.
--
--   Specifically, for any $d, k \in \mathbb{N}$ and $S : \operatorname{List}(\operatorname{List} \mathbb{N})$, there exists a $d$-polytope $P \subseteq \mathbb{R}^d$ realizing $S$ if and only if there exists a configuration $V : \operatorname{Fin} k \to \mathbb{R}^d$ satisfying:
--   1. **Nonemptiness and injectivity:** $k > 0$ and $V$ is injective (`Function.Injective V`);
--   2. **Full affine span by affine combinations:** For every $x \in \mathbb{R}^d$, there exist weights $w : \operatorname{Fin} k \to \mathbb{R}$ with $\sum_{i=0}^{k-1} w_i = 1$ and $\sum_{i=0}^{k-1} w_i V_{i,t} = x_t$ for all $t \in \operatorname{Fin} d$;
--   3. **Strict support at each vertex:** For every $i \in \operatorname{Fin} k$, there exists $a \in \mathbb{R}^d$ such that $\sum_t a_t V_{j,t} < \sum_t a_t V_{i,t}$ for all $j \neq i$;
--   4. **Label range bound:** Every label $n$ occurring in a row $L \in S$ satisfies $n < k$; and
--   5. **Exact powerset support certificates:** For every subset $J \subseteq \{0, \dots, k - 1\}$, $J$ occurs as `L.toFinset` for some $L \in S$ if and only if $J \neq \emptyset$, $J \neq \{0, \dots, k - 1\}$, and there exist $a \in \mathbb{R}^d$ and $b \in \mathbb{R}$ such that
--      $$
--      \forall i \in \operatorname{Fin} k,\quad \sum_{t=0}^{d-1} a_t V_{i,t} \le b \quad\text{and}\quad \left(\sum_{t=0}^{d-1} a_t V_{i,t} = b \iff i \in J\right).
--      $$
--
--   **Formalization Note** Every quantifier over infinite geometric objects ($P$, `IsExposed ℝ P F`, `affineSpan ℝ P = ⊤`) is eliminated in favor of finitely many real variables ($V_{i,t}, w_i, a_t, b$) and finite conjunctions/disjunctions over $\operatorname{Fin} k$, $\operatorname{Fin} d$, and $(\operatorname{Finset.range} k).\mathrm{powerset}$.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed., Graduate Texts in Mathematics 221), §5.5, pp. 90–91, Theorem 5.5.2

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_SchemeRealizes
import Theorems.Thm_Grunbaum2003_polytope_face_eq_convexHull_exposed_vertices
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.AffineSpace.Combination
import Mathlib.LinearAlgebra.Pi

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

theorem exists_schemeRealizes_iff_arithmetic_certificates (d k : ℕ)
    (S : List (List ℕ)) :
    (∃ P : Set (Fin d → ℝ), SchemeRealizes k S P) ↔
    ∃ V : Fin k → Fin d → ℝ,
      0 < k ∧ Function.Injective V ∧
      (∀ x : Fin d → ℝ, ∃ w : Fin k → ℝ,
        (∑ i, w i) = 1 ∧ ∀ t : Fin d, (∑ i, w i * V i t) = x t) ∧
      (∀ i : Fin k, ∃ a : Fin d → ℝ, ∀ j : Fin k, j ≠ i →
        (∑ t, a t * V j t) < ∑ t, a t * V i t) ∧
      (∀ L ∈ S, ∀ n ∈ L, n < k) ∧
      ∀ J ∈ (Finset.range k).powerset,
        (∃ L ∈ S, L.toFinset = J) ↔
          J.Nonempty ∧ J ≠ Finset.range k ∧
            ∃ (a : Fin d → ℝ) (b : ℝ),
              (∀ i : Fin k, (∑ t, a t * V i t) ≤ b) ∧
              (∀ i : Fin k, (∑ t, a t * V i t) = b ↔ i.val ∈ J) := by sorry

end Grunbaum2003
