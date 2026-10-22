-- Prove2me | Theorems.Thm_GeomDL_WL_gnn_le_wl
-- name    : GeomDL.WL.gnn_le_wl
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:42:06.54189+00:00
-- url     : https://prove2.me/theorems/68a41915-e702-4894-aa02-6eaaf366edeb
-- title:
--   Ch. 7, p. 120 — message-passing GNNs are no more powerful than the Weisfeiler–Lehman test
-- statement:
--   Let $N$ be a message-passing GNN with layers (35), constant initial features $h^0_u = c$, and parameters shared by all graphs; let $\mathrm{readout}$ be any function of a multiset of node features, $T \ge 0$ a depth, and $G$, $G'$ two graphs (possibly with different numbers of nodes). Write $c^t_G(u)$ for the round-$t$ Weisfeiler–Lehman colour of the node $u$ of $G$. Then:
--
--   1. (node level) for every $t \le T$ and all nodes $u$ of $G$, $v$ of $G'$,
--   $$
--   c^t_G(u) = c^t_{G'}(v) \implies h^t_G(u) = h^t_{G'}(v);
--   $$
--   2. (graph level) if the round-$T$ WL colour histograms agree, $\{\!\{c^T_G(u)\}\!\}_u = \{\!\{c^T_{G'}(v)\}\!\}_v$, then
--   $$
--   \mathrm{readout}\big(\{\!\{h^T_G(u)\}\!\}_u\big) = \mathrm{readout}\big(\{\!\{h^T_{G'}(v)\}\!\}_v\big).
--   $$
--
--   Every pair of graphs the GNN separates is therefore separated by the WL test.
--
--   **Formalization Note** The page says "any GNN conforming to one of the three flavours". The statement is posed for the message-passing flavour (35), which contains the attentional flavour (34) and the convolutional flavour (33) when the coefficient $c_{uv}$ is a function of the features of $u$ and $v$. A coefficient that is an arbitrary function of the graph (for instance the number of triangles through $u$) falls outside the claim, and the claim is false for it. Graphs are featureless, as in the WL analyses (side-note p. 120); the WL test is the reused `neighborColor` / `neighborHistogram`.
-- source:
--   Bronstein et al., Geometric Deep Learning (arXiv:2104.13478v2), Ch. 7, "The Weisfeiler-Lehman formalism", p. 120, "any GNN conforming to one of the three flavours we outlined in Section 5.3 cannot be more powerful than the WL test!"

import Mathlib
import Definitions.Def_WLIdentification
import Definitions.Def_GeomDL_WL_Defs

namespace GeomDL.WL
open OAI.WLIdentification

/-- Ch. 7, p. 120: a message-passing GNN (35) with constant initial features cannot be more powerful
than the Weisfeiler–Lehman test. For one GNN `N` (parameters shared across graphs) and any two
graphs `G`, `G'`: (1) two nodes with equal round-`t` WL colours have equal round-`t` features,
for every `t ≤ T`; (2) if the round-`T` WL colour histograms agree, every read-out of the
round-`T` node features agrees. -/
theorem gnn_le_wl {F M A Y : Type*} (N : GNN F M A) (readout : Multiset F → Y) (T : ℕ)
    (G G' : Graph) :
    (∀ t ≤ T, ∀ u v, neighborColor G t u = neighborColor G' t v →
        N.features G t u = N.features G' t v) ∧
      (neighborHistogram G T = neighborHistogram G' T →
        N.output readout G T = N.output readout G' T) := by sorry

end GeomDL.WL
