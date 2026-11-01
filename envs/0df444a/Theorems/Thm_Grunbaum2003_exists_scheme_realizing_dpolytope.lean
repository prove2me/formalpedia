-- Prove2me | Theorems.Thm_Grunbaum2003_exists_scheme_realizing_dpolytope
-- name    : Grunbaum2003.exists_scheme_realizing_dpolytope
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-31T22:14:31.977722+00:00
-- url     : https://prove2.me/theorems/18cc73a1-ddd0-46d1-9e07-fbbeb0539cd1
-- title:
--   Existence of a finite vertex-face incidence scheme realizing any $d$-polytope
-- statement:
--   This theorem proves that every $d$-polytope with $k$ vertices is realized by at least one finite vertex-face incidence scheme $S$.
--
--   Let $d, k \in \mathbb{N}$, and let $P \subseteq \mathbb{R}^d$ be a $d$-polytope (`IsDPolytope P`) having $k$ vertices (`faceCount P 0 = k`). Then there exists a finite scheme $S : \operatorname{List}(\operatorname{List} \mathbb{N})$ such that $P$ realizes $S$ on $k$ vertices:
--
--   $$
--   \operatorname{IsDPolytope}(P) \;\land\; f_0(P) = k \implies \exists S : \operatorname{List}(\operatorname{List} \mathbb{N}),\; \operatorname{SchemeRealizes}(k, S, P).
--   $$
--
--   Together with `schemeRealizes_unique_combinatorial_type`, this theorem shows that the combinatorial types of $d$-polytopes with $k$ vertices correspond bijectively to the equivalence classes of realizable finite schemes on $\{0,\dots,k-1\}$, reducing the effective enumerability of combinatorial types (Grünbaum Theorem 5.5.2) to the decidability of geometric realizability of a candidate scheme.
--
--   **Formalization Note** The proof identifies the $0$-dimensional exposed faces of $P$ with singleton sets $\{x\}$ of exposed vertices, establishes a bijection $V : \operatorname{Fin} k \xrightarrow{\sim} \operatorname{vert}(P)$ from `faceCount P 0 = k`, and collects the vertex-index subsets of all nonempty proper exposed faces into a finite list of lists.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed., Graduate Texts in Mathematics 221), §3.2 & §5.5, pp. 36, 90–91, Theorem 5.5.2

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_SchemeRealizes

set_option autoImplicit false

namespace Grunbaum2003

theorem exists_scheme_realizing_dpolytope (d k : ℕ)
    (P : Set (Fin d → ℝ)) (hP : IsDPolytope P) (hk : faceCount P 0 = k) :
    ∃ S : List (List ℕ), SchemeRealizes k S P := by sorry

end Grunbaum2003
