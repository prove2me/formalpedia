-- Prove2me | Theorems.Thm_Grunbaum2003_simplicial_g_theorem_one_dim
-- name    : Grunbaum2003.simplicial_g_theorem_one_dim
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-02T07:15:32.763854+00:00
-- url     : https://prove2.me/theorems/13e3b96d-8b08-49b4-b12b-f8b7dd0a860d
-- title:
--   One-dimensional Billera–Lee–Stanley $g$-theorem ($d = 1$)
-- statement:
--   This theorem proves the exact $1$-dimensional specialization ($d = 1$) of the Billera–Lee–Stanley $g$-theorem (`simplicial_g_theorem`).
--
--   Let $f = (f_0, f_1) : \operatorname{Fin}(1 + 1) \to \mathbb{Z}$. Then $f(0) = 1$ and there exists a simplicial $1$-polytope $P \subseteq \mathbb{R}^1$ (`IsSimplicialDPolytope P`) with $f(1) = f_0(P)$ if and only if there exists an $M$-sequence $g : \mathbb{N} \to \mathbb{N}$ of length $\lfloor 1/2 \rfloor + 1 = 1$ (`IsMSequence (1 / 2) g`) such that
--   $$
--   \forall k \in \{0, 1\},\quad f(k) = \sum_{j=0}^{\lfloor 1/2 \rfloor} g_j \, M_1(j, k).
--   $$
--
--   Both sides are equivalent to $f(0) = 1 \land f(1) = 2$:
--   - Geometrically, every $1$-polytope $P \subseteq \mathbb{R}^1$ has face lattice isomorphic to the diamond $\{0 < 1, 2 < 3\}$ (`one_dimensional_face_equiv`), so $P$ has exactly two $0$-dimensional faces (`one_dimensional_faceCount_zero : faceCount P 0 = 2`) and is automatically simplicial (`isSimplicialDPolytope_one_of_isDPolytope`), realized by the unit segment $\operatorname{conv}\{0, 1\} \subseteq \mathbb{R}^1$ (`exists_simplicial_segment`).
--   - Arithmetically, `g_theorem_rhs_dim_one_iff` reduces the right-hand side to $f(0) = 1 \land f(1) = 2$.
--
--   **Formalization Note** Combining this $d = 1$ theorem with `gTheoremMatrix_col_zero_sum_and_zero_dim` ($d = 0$) leaves only $d \ge 2$ (`simplicial_g_theorem_ge_two`) in `simplicial_g_theorem_pos_dim_tail`.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed., Graduate Texts in Mathematics 221), §10.6, pp. 198a–198b

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_BoundaryRefines
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_IsMSequence
import Definitions.Def_Grunbaum2003_gTheoremMatrix
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.DiscreteSubset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

theorem simplicial_g_theorem_one_dim (f : Fin (1 + 1) → ℤ) :
    (f 0 = 1 ∧ ∃ P : Set (Fin 1 → ℝ),
      IsSimplicialDPolytope P ∧
      ∀ j : Fin 1, f j.succ = (faceCount P j.val : ℤ)) ↔
    ∃ g : ℕ → ℕ, IsMSequence (1 / 2) g ∧
      ∀ k : Fin (1 + 1),
        f k = ∑ j ∈ Finset.range (1 / 2 + 1),
          (g j : ℤ) * gTheoremMatrix 1 j k.val := by sorry

end Grunbaum2003
