-- Prove2me | Theorems.Thm_MetricGenerators_FewComponents_claim
-- name    : MetricGenerators.FewComponents.claim
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:01:22.756093+00:00
-- url     : https://prove2.me/theorems/1397217b-72ac-4411-9198-677802c978e4
-- title:
--   Claim in the proof of Theorem 5 (p. 391): G has a minimum T-join with at most q components iff the 3DM instance has a matching M ⊆ H
-- statement:
--   Let $W$, $X$, $Y$ be three disjoint sets of cardinality $q$, let $H\subseteq W\times X\times Y$, and let $G$ and $T=W\cup X\cup Y\cup Z$ be the graph and the $4q$-element vertex set that Sebő and Tannier build from this 3DM instance. Then
--
--   $$\exists\, F\ \text{a minimum } T\text{-join of } G \text{ with at most } q \text{ connected components}\iff \exists\, M\subseteq H \text{ a matching}.$$
--
--   This Claim is the mathematical content of Theorem 5 of the paper, which states that MTSC is NP-complete: deciding whether a minimum $T$-join has at most $k$ components is at least as hard as THREE-DIMENSIONAL MATCHING.
--
--   **Formalization Note.** Only the correctness of the reduction is formalized; membership in NP and polynomial-time computability are not. "Minimum" is over all $T$-joins of $G$, and components are those of the graph $(V(F),F)$. The statement covers $q=0$, where both sides hold trivially.
-- source:
--   Sebő and Tannier, On Metric Generators of Graphs, Math. Oper. Res. 29(2):383–393 (2004), DOI 10.1287/moor.1030.0070, p. 391, §3.1, proof of Theorem 5, Claim

import Mathlib
import Definitions.Def_MetricGenerators_FewComponents_TJoin
import Definitions.Def_MetricGenerators_FewComponents_ThreeDM
import Definitions.Def_MetricGenerators_FewComponents_Gadget

namespace MetricGenerators.FewComponents

/-- The Claim in the proof of Theorem 5 (Sebő and Tannier, On Metric Generators of Graphs, Math.
Oper. Res. 29(2):383–393 (2004), §3.1, proof of Theorem 5, Claim, p. 391): "There exists a minimum
T-join with at most q connected components in G if and only if there exists a matching M ⊆ H."

Here `G = gadget q H` and `T = gadgetT q H` are the graph and the vertex set `W ∪ X ∪ Y ∪ Z`
constructed on p. 390 from the 3DM instance `(W, X, Y, H)`, `|W| = |X| = |Y| = q`.

**Formalization Note.** This is the mathematical content of the reduction from 3DM; Theorem 5's
complexity statement ("MTSC is NP-complete") is not formalized. "Minimum" is over all `T`-joins of
`G`; the components are those of the graph `(V(F), F)`. The statement holds for every `q`,
including `q = 0` (empty graph, `F = ∅` with `0` components, `M = ∅`). -/
theorem claim (q : ℕ) (H : Finset (Fin q × Fin q × Fin q)) :
    (∃ F : Finset (Sym2 (GVert q H)),
        IsMinTJoin (gadget q H) (gadgetT q H) F ∧ numComponents F ≤ q) ↔
      ∃ M ⊆ H, IsMatching q M := by sorry

end MetricGenerators.FewComponents
