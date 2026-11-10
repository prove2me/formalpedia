-- Prove2me | Theorems.Thm_OnlineTransportation1195_Main_root_patch_normalization_iff
-- name    : OnlineTransportation1195.Main.root_patch_normalization_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T23:36:19.909388+00:00
-- url     : https://prove2.me/theorems/2e18b675-ea8f-44ef-905d-b2e88340be24
-- title:
--   Claim 3.4 — root-patch normalization equivalence
-- statement:
--   Let $T$, its deadlines and its fixed DFS satisfy the Section 3 positive-weight, monotone-positive-deadline and normalization assumptions. For $t>0$ and $0<s\le t$,
--
--   $$\sum_{e\in T_r(t)}\frac{w_e}{\min\{d_e,s\}}=1\quad\Longleftrightarrow\quad R^{\rm in}(t)=F(s).$$
--
--   Both directions are asserted, including when the root patch is empty. The parameters $s,t$ do not change the initial DFS.
--
--   Differences from the source:
--   - encoding: finite rooted trees and undirected edges → vertices Fin n and non-root child labels for edges in the referenced positive tree record; reason: every finite rooted positive weighted tree admits this labeling; the root pseudo-edge is ignored
--   - encoding: any fixed root-based depth-first walk and its first-edge downward costs → a vertex list traversing each edge once in each direction; computed x, red edges and root patch; reason: on a tree these are exactly the depth-first tours; the list is fixed before time budgets are quantified
-- source:
--   Anand et al., STOC 2027 submission #1195 (October 2026), Claim 3.4, PDF / printed p. 10; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1195.pdf

import Definitions.Def_OnlineTransportation1195_Main_RedPatches

namespace OnlineTransportation1195.Main

theorem root_patch_normalization_iff {n : ℕ} (T : Tree n) (d : Fin n → ℝ)
    (L : List (Fin n)) (hD : T.Normalized d) (hDFS : T.DFS L)
    (s t : ℝ) (ht : 0 < t) (hs : 0 < s) (hst : s ≤ t) :
    T.patchNormalization d L s t = 1 ↔ T.Rin d L t = T.F d s := by sorry

end OnlineTransportation1195.Main
