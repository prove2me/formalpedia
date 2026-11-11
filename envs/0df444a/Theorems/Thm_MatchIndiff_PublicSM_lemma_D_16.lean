-- Prove2me | Theorems.Thm_MatchIndiff_PublicSM_lemma_D_16
-- name    : MatchIndiff.PublicSM.lemma_D_16
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:26:34.309199+00:00
-- url     : https://prove2.me/theorems/f40a8520-598c-4f40-b724-b051d47646d0
-- title:
--   Lemma D.16 — the lexicographically first perfect matching has a row-local O(m log(m + 1))-bit certificate
-- statement:
--   Consider a bipartite graph with $m$ rows and $m$ columns with public identifiers, in which each row privately knows only its allowed columns. Then the lexicographically first perfect matching has a joint verification certificate, including the matching, of at most
--   $$3m\lceil\log_2(m+1)\rceil$$
--   bits: there is a board alphabet of size $c$ with $\lceil\log_2 c\rceil\le 3m\lceil\log_2(m+1)\rceil$ and, for each row, a decoder and a check that see only that row's allowed columns and the board, such that on every graph that has a perfect matching some board is accepted by all rows and decodes the lexicographically first perfect matching, and every board accepted by all rows decodes it.
--
--   It certifies the canonical exact matching inside a verified rank class (Theorem D.8, strong case).
--
--   Differences from the source:
--   - generalization: an O(m log(m + 1))-bit certificate → an explicit bound 3m⌈log₂(m+1)⌉ on ⌈log₂ c⌉; reason: an explicit constant implies the O-bound; the paper's certificate is a column, a parent pointer and a sibling position per row
--   - reading: the lexicographically first perfect matching has a certificate checked by every row → a complete and sound joint verification protocol on the set of graphs that have a perfect matching, each row's output its matched column; reason: the lexicographically first perfect matching exists exactly on those graphs
--   - encoding: rows and columns with public identifiers, private allowed columns → rows and columns Fin m in index order, private input G i : Fin m → Bool, board alphabet Fin c; reason: Lean convention
-- source:
--   Zhang, Zhao, Xu, Xi, Zhao, Structural Complexity of Matching with Indifferences, STOC 2027 submission (manuscript sha256 22dfb437…), p. 98, Lemma D.16

import Mathlib
import Definitions.Def_MatchIndiff_PublicSM_Protocol
import Definitions.Def_MatchIndiff_PublicSM_Forest

namespace MatchIndiff.PublicSM

/-- Lemma D.16 (p. 98): in a bipartite graph with `m` private rows (row `i` knows only its allowed
columns `G i`) and `m` public columns, the lexicographically first perfect matching has a joint
verification certificate, including the matching, of at most `3m⌈log₂(m+1)⌉` bits, checked by each
row from its own allowed columns and the board, on every graph that has a perfect matching. -/
theorem lemma_D_16 (m : ℕ) :
    ∃ (c : ℕ) (p : VerifProtocol (fun _ : Fin m => Fin m → Bool) (fun _ : Fin m => Fin m) (Fin c)),
      p.IsJV {G | ∃ π, IsPM G π} (fun G i => lexFirstPM G i) ∧
        Nat.clog 2 c ≤ 3 * m * Nat.clog 2 (m + 1) := by sorry

end MatchIndiff.PublicSM
