-- Prove2me | Theorems.Thm_MetricGenerators_ConnectedJoin_minimal_tjoin_paths
-- name    : MetricGenerators.ConnectedJoin.minimal_tjoin_paths
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:49:44.319468+00:00
-- url     : https://prove2.me/theorems/4b77205d-5da4-4f92-8c10-23df93edac9f
-- title:
--   §3, p. 389 — a minimal T-join is the edge-disjoint union of |T|/2 paths pairing the vertices of T
-- statement:
--   Let $G$ be a connected finite graph, let $T\subseteq V(G)$ have even cardinality, and let $F$ be an inclusionwise minimal $T$-join of $G$. Put $m=|T|/2$. Then the vertices of $T$ can be listed as $2m$ distinct vertices $s_1,t_1,\dots,s_m,t_m$, and there are paths $P_1,\dots,P_m$ in $G$, $P_i$ joining $s_i$ and $t_i$, such that
--
--   $$F=E(P_1)\cup\dots\cup E(P_m),\qquad E(P_i)\cap E(P_j)=\emptyset\ (i\neq j).$$
--
--   The paper records this fact at the start of §3 and uses it in the sufficiency half of Lemma 2, applied to a minimum $T$-join.
--
--   **Formalization Note.** "Minimal" is inclusionwise minimality and "disjoint" is edge-disjoint, as the paper restates it on p. 392. The pairing is encoded as an injective map from two copies of $\{1,\dots,m\}$ to $V$ whose image is $T$; the paths are `Walk`s of $G$ that are paths.
-- source:
--   Sebő and Tannier, On Metric Generators of Graphs, Math. Oper. Res. 29(2):383–393 (2004), DOI 10.1287/moor.1030.0070, p. 389, §3 (unnumbered)

import Mathlib
import Definitions.Def_MetricGenerators_ConnectedJoin_TJoin

namespace MetricGenerators.ConnectedJoin

/-- **§3, p. 389 (unnumbered).** "It is useful to know and easy to check that a minimal T-join is
the disjoint union of |T|/2 paths pairing the vertices of T." (Sebő and Tannier, On Metric
Generators of Graphs, Math. Oper. Res. 29(2):383–393 (2004), DOI 10.1287/moor.1030.0070, p. 389.)

Let `G` be a connected graph, `T` a vertex set of even cardinality and `F` an inclusionwise
minimal `T`-join. With `m = |T|/2`, there are vertices `s i, t i` (`i < m`), all `2m` of them
distinct and together forming `T`, and paths `P i` of `G` from `s i` to `t i`, pairwise
edge-disjoint, whose edges together are exactly `F`.

**Formalization Note.** "Minimal" is inclusionwise minimality (`IsMinimalTJoin`); "disjoint" is
edge-disjoint (as p. 392 restates it: "J is the edge-disjoint union of m := |T|/2 paths"). The
pairing is the injective map `Sum.elim s t : Fin m ⊕ Fin m → V` with range `T`. -/
theorem minimal_tjoin_paths {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hG : G.Connected) (T : Finset V) (hT : Even T.card) (F : Finset (Sym2 V))
    (hF : IsMinimalTJoin G T F) :
    ∃ (s t : Fin (T.card / 2) → V) (P : ∀ i, G.Walk (s i) (t i)),
      Function.Injective (Sum.elim s t) ∧
      Set.range (Sum.elim s t) = (↑T : Set V) ∧
      (∀ i, (P i).IsPath) ∧
      (∀ i j, i ≠ j → Disjoint (P i).edges.toFinset (P j).edges.toFinset) ∧
      Finset.univ.biUnion (fun i => (P i).edges.toFinset) = F := by sorry

end MetricGenerators.ConnectedJoin
