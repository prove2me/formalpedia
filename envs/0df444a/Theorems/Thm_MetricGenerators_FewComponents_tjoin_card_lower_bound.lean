-- Prove2me | Theorems.Thm_MetricGenerators_FewComponents_tjoin_card_lower_bound
-- name    : MetricGenerators.FewComponents.tjoin_card_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:01:26.491552+00:00
-- url     : https://prove2.me/theorems/d3911e41-f842-4889-8120-080860c777d7
-- title:
--   Proof of Theorem 5, p. 391: every T-join of G has at least |T| = 4q edges, with equality iff exactly one edge at each t ∈ T
-- statement:
--   Let $G$ and $T=W\cup X\cup Y\cup Z$ be the graph and the vertex set built from an instance $(W,X,Y,H)$ of 3DM with $|W|=|X|=|Y|=q$. Then every $T$-join $F$ of $G$ satisfies
--
--   $$|F|\ \ge\ |T|=4q,$$
--
--   and $|F|=4q$ holds if and only if every $t\in T$ is incident to exactly one edge of $F$.
--
--   This is the preliminary remark of the proof that minimum $T$-joins of $G$ with few components correspond to matchings. The paper's reason is that $T$ induces no edge of $G$.
-- source:
--   Sebő and Tannier, On Metric Generators of Graphs, Math. Oper. Res. 29(2):383–393 (2004), DOI 10.1287/moor.1030.0070, p. 391, §3.1, proof of Theorem 5, first paragraph after the Claim

import Mathlib
import Definitions.Def_MetricGenerators_FewComponents_TJoin
import Definitions.Def_MetricGenerators_FewComponents_Gadget

namespace MetricGenerators.FewComponents

/-- Lower bound on the size of a `T`-join of the graph `G` of the proof of Theorem 5 (Sebő and
Tannier, On Metric Generators of Graphs, Math. Oper. Res. 29(2):383–393 (2004), §3.1, proof of
Theorem 5, p. 391, unnumbered): "Since T does not induce any edge, every T-join F must contain at
least |T| = 4q edges, and the equality holds if and only if F contains exactly one edge incident to
each t ∈ T."

**Formalization Note.** "`F` contains exactly one edge incident to `t`" is `edgeDeg F t = 1`. -/
theorem tjoin_card_lower_bound (q : ℕ) (H : Finset (Fin q × Fin q × Fin q))
    (F : Finset (Sym2 (GVert q H))) (hF : IsTJoin (gadget q H) (gadgetT q H) F) :
    4 * q ≤ F.card ∧ (F.card = 4 * q ↔ ∀ t ∈ gadgetT q H, edgeDeg F t = 1) := by sorry

end MetricGenerators.FewComponents
