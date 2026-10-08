-- Prove2me | Theorems.Thm_MetricGenerators_FewComponents_min_tjoin_components
-- name    : MetricGenerators.FewComponents.min_tjoin_components
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:01:32.433153+00:00
-- url     : https://prove2.me/theorems/af34fb2f-b9fc-45a5-b66c-0213108bd6e9
-- title:
--   Proof of Theorem 5, p. 391: a minimum T-join of G has ≥ q components, with equality iff each has an H-vertex and one vertex of each of W, X, Y
-- statement:
--   Let $G$ and $T$ be built from an instance $(W,X,Y,H)$ of 3DM with $|W|=|X|=|Y|=q$, and let $F$ be a minimum $T$-join of $G$. Then $F$ has at least $q$ connected components:
--
--   $$\#\mathrm{comp}(F)\ \ge\ q.$$
--
--   Moreover, $\#\mathrm{comp}(F)=q$ if and only if every connected component of $F$ contains a vertex of $H$ and exactly one vertex of each of $W$, $X$ and $Y$.
--
--   In the proof of Theorem 5 this is the step that turns a minimum $T$-join with at most $q$ components into a matching.
--
--   **Formalization Note.** Components are those of the graph $(V(F),F)$. The paper supports this conclusion with the remark that the non-$T$ end $h$ of an edge of $F$ "is adjacent to at most one vertex in each of $W$, $X$, $Y$". That remark fails when $h$ is the midpoint of the path joining two vertices of the same class. Only the conclusion is stated here, and it is true.
-- source:
--   Sebő and Tannier, On Metric Generators of Graphs, Math. Oper. Res. 29(2):383–393 (2004), DOI 10.1287/moor.1030.0070, p. 391, §3.1, proof of Theorem 5, fourth paragraph after the Claim (last sentence)

import Mathlib
import Definitions.Def_MetricGenerators_FewComponents_TJoin
import Definitions.Def_MetricGenerators_FewComponents_Gadget

namespace MetricGenerators.FewComponents

/-- Component count of a minimum `T`-join of the graph `G` of the proof of Theorem 5 (Sebő and
Tannier, On Metric Generators of Graphs, Math. Oper. Res. 29(2):383–393 (2004), §3.1, proof of
Theorem 5, p. 391, unnumbered; the last sentence of the paragraph): "It follows that F has at
least q components and the equality holds if and only if each component of F contains a vertex in
H and exactly one vertex from each of W, X, and Y."

**Formalization Note.** Only this conclusion is stated. The paper's intermediate sentence "h is
adjacent to at most one vertex in each of W, X, Y" fails when `h` is the midpoint of the path
joining two vertices of the same class (the conclusion is still true). A component of `F` is a
component of the graph `(V(F), F)`, represented by an element `c` of `components F`; "`v` lies
in `c`" is `(edgeGraph F).connectedComponentMk v = c`. The classes `W`, `X`, `Y` are the
`T`-vertices `t (i, j)` with `i = 0, 1, 2`. -/
theorem min_tjoin_components (q : ℕ) (H : Finset (Fin q × Fin q × Fin q))
    (F : Finset (Sym2 (GVert q H))) (hF : IsMinTJoin (gadget q H) (gadgetT q H) F) :
    q ≤ numComponents F ∧
      (numComponents F = q ↔
        ∀ c ∈ components F,
          (∃ m : ↥H, (edgeGraph F).connectedComponentMk (GVert.h m) = c) ∧
          ∀ i : Fin 4, i ≠ 3 →
            ∃! j : Fin q, (edgeGraph F).connectedComponentMk (GVert.t (i, j)) = c) := by sorry

end MetricGenerators.FewComponents
