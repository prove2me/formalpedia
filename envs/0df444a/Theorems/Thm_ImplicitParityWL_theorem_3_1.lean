-- Prove2me | Theorems.Thm_ImplicitParityWL_theorem_3_1
-- name    : ImplicitParityWL.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:17:20.081218+00:00
-- url     : https://prove2.me/theorems/4e0a34ab-0ac6-4c1a-8859-99e16f96a940
-- title:
--   Theorem 3.1 — pebble game and $k$-WL round correspondence
-- statement:
--   Let $k\ge2$, let $G,H$ be colored graphs and let $r\ge0$.
--
--   1. If Spoiler wins $\mathrm{BP}_{k+1}(G,H)$ within $r$ rounds, then $k$-WL distinguishes $G$ and $H$ after at most $r$ rounds.
--   2. If $k$-WL distinguishes $G$ and $H$ after $r$ rounds, then Spoiler wins $\mathrm{BP}_{k+1}(G,H)$ within $r+k$ rounds.
--
--   In particular, Duplicator wins $\mathrm{BP}_{k+1}(G,H)$ if and only if $k$-WL does not distinguish $G$ and $H$.
--
--   This transfers all round bounds of the paper from the game to the algorithm, with both offsets used numerically. The paper cites the theorem ([20, 52, 50]; see also [36, 56]) and gives no proof.
--
--   Differences from the source:
--   - encoding: k-WL distinguishes G and H after at most r rounds → ∃ r' ≤ r, DistinguishesAfter G H k r'; reason: the page's phrase, written out; distinguishing is monotone in r
-- source:
--   Curticapean, Liu, Neuen, Seppelt, Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems (STOC 2027 submission, manuscript of November 3, 2026, sha256 6604ccc9…), Theorem 3.1, p.15

import Mathlib
import Definitions.Def_ImplicitParityWL_WLColor
import Definitions.Def_ImplicitParityWL_PebbleGame

namespace ImplicitParityWL

/-- **Theorem 3.1** (Curticapean, Liu, Neuen, Seppelt, *Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems*, manuscript of November 3, 2026, p.15): for `k ≥ 2` and colored graphs `G`, `H`,
(1) if Spoiler wins `BP_{k+1}(G, H)` within `r` rounds, then `k`-WL distinguishes `G` and `H` after at most
`r` rounds; (2) if `k`-WL distinguishes them after `r` rounds, then Spoiler wins `BP_{k+1}(G, H)` within
`r + k` rounds; and Duplicator wins `BP_{k+1}(G, H)` if and only if `k`-WL does not distinguish `G` and `H`.

The paper cites this theorem ([20, 52, 50]; see also [36, 56]) and gives no proof. -/
theorem theorem_3_1 {K V W : Type*} [Fintype V] [Fintype W] (G : ColoredGraph K V)
    (H : ColoredGraph K W) (k : ℕ) (hk : 2 ≤ k) :
    (∀ r : ℕ, SpoilerWinsWithin (k + 1) G H r → ∃ r' ≤ r, DistinguishesAfter G H k r') ∧
    (∀ r : ℕ, DistinguishesAfter G H k r → SpoilerWinsWithin (k + 1) G H (r + k)) ∧
    ((∀ r : ℕ, ¬ SpoilerWinsWithin (k + 1) G H r) ↔ ∀ r : ℕ, ¬ DistinguishesAfter G H k r) := by sorry

end ImplicitParityWL
