-- Prove2me | Theorems.Thm_MetricGenerators_FewComponents_min_tjoin_card
-- name    : MetricGenerators.FewComponents.min_tjoin_card
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:01:30.551981+00:00
-- url     : https://prove2.me/theorems/4f157a2b-e3bd-4742-9f22-8f2b3eb474ec
-- title:
--   Proof of Theorem 5, p. 391: a minimum T-join F of G has |F| = 4q, and every t ∈ T lies in exactly one edge of F
-- statement:
--   Let $G$ and $T$ be built from an instance $(W,X,Y,H)$ of 3DM with $|W|=|X|=|Y|=q$, and let $F$ be a minimum $T$-join of $G$. Then
--
--   $$|F|=4q,$$
--
--   and every $t\in T$ is incident to exactly one edge of $F$.
--
--   The paper's argument pairs up the vertices of $T$ and takes the paths of length 2 between the pairs, which gives a $T$-join of size $4q$. The preliminary lower bound then forces equality.
-- source:
--   Sebő and Tannier, On Metric Generators of Graphs, Math. Oper. Res. 29(2):383–393 (2004), DOI 10.1287/moor.1030.0070, p. 391, §3.1, proof of Theorem 5, fourth paragraph after the Claim

import Mathlib
import Definitions.Def_MetricGenerators_FewComponents_TJoin
import Definitions.Def_MetricGenerators_FewComponents_Gadget

namespace MetricGenerators.FewComponents

/-- A minimum `T`-join of the graph `G` of the proof of Theorem 5 has exactly `4q` edges, one at
each vertex of `T` (Sebő and Tannier, On Metric Generators of Graphs, Math. Oper. Res.
29(2):383–393 (2004), §3.1, proof of Theorem 5, p. 391, unnumbered): "Partitioning T in 2q pairs
in an arbitrary way, and taking the union of paths of length 2 between all pairs, we get a T-join
of size 4q; consequently |F| ≤ 4q. We now get |F| = 4q from the preliminary remark, and also that
every t ∈ T is then incident to exactly one edge th of F."

**Formalization Note.** "`F` is a minimum `T`-join" is `IsMinTJoin` (minimum over all
`T`-joins of `G`); "incident to exactly one edge" is `edgeDeg F t = 1`. -/
theorem min_tjoin_card (q : ℕ) (H : Finset (Fin q × Fin q × Fin q))
    (F : Finset (Sym2 (GVert q H))) (hF : IsMinTJoin (gadget q H) (gadgetT q H) F) :
    F.card = 4 * q ∧ ∀ t ∈ gadgetT q H, edgeDeg F t = 1 := by sorry

end MetricGenerators.FewComponents
