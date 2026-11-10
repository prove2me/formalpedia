-- Prove2me | Theorems.Thm_OnlineTransportation1195_Main_detour_budget_inequality
-- name    : OnlineTransportation1195.Main.detour_budget_inequality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T23:36:16.716203+00:00
-- url     : https://prove2.me/theorems/baa33300-3101-4e3e-9c00-f5a18bec8af4
-- title:
--   Claim 3.5 — detour budget inequality
-- statement:
--   Let $T$ have positive edge weights and root-monotone positive deadlines normalized by $\sum_e w_e/d_e=1$. Fix a root-based DFS. For $t>0$ and $0<s\le t$ satisfying $R^{\rm in}(t)=F(s)$,
--
--   $$R(t)\le F(t)\quad\Longrightarrow\quad s+R^{\rm out}(t)\le t.$$
--
--   This is the source implication with its complete parameter domain and its computed red-weight functions.
--
--   Differences from the source:
--   - encoding: finite rooted trees and undirected edges → vertices Fin n and non-root child labels for edges in the referenced positive tree record; reason: every finite rooted positive weighted tree admits this labeling; the root pseudo-edge is ignored
--   - encoding: any fixed root-based depth-first walk and its first-edge downward costs → a vertex list traversing each edge once in each direction; computed x, red edges and root patch; reason: on a tree these are exactly the depth-first tours; the list is fixed before time budgets are quantified
-- source:
--   Anand et al., STOC 2027 submission #1195 (October 2026), Claim 3.5, PDF / printed p. 11; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1195.pdf

import Definitions.Def_OnlineTransportation1195_Main_RedPatches

namespace OnlineTransportation1195.Main

theorem detour_budget_inequality {n : ℕ} (T : Tree n) (d : Fin n → ℝ)
    (L : List (Fin n)) (hD : T.Normalized d) (hDFS : T.DFS L)
    (s t : ℝ) (ht : 0 < t) (hs : 0 < s) (hst : s ≤ t)
    (heq : T.Rin d L t = T.F d s) :
    T.R d L t ≤ T.F d t → s + T.Rout d L t ≤ t := by sorry

end OnlineTransportation1195.Main
