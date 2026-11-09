-- Prove2me | Theorems.Thm_MMSImpossibility_Goods_lemma_7
-- name    : MMSImpossibility.Goods.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:18:02.21268+00:00
-- url     : https://prove2.me/theorems/c9f97b9b-c77b-4c34-84ae-984c6b0a9f43
-- title:
--   Lemma 7 — the low-good sets of auxiliary weight $H$ are $\{G_h\}$ and $\{X_j, Y_j\}$
-- statement:
--   Throughout, $n \ge 2^{16}$, $k = 8\lceil \log_2 n\rceil$, and the instance of §2.1 has $m = n+5k$ goods: $Z_j, X_j, Y_j$ ($0\le j<2k$), $G_h$ ($0\le h<k$), $P$, $Q$ and $D_t$ ($1\le t\le n-2k-2$), with auxiliary weights $w$ and, for an agent of type $S$, valuation $v_S(g) = 3w(g)+\rho_S(g)$ (equation (3)); $\mu = 3T = 204k^3$ and $\ell = k/24$.
--
--   A set $B$ of low goods (goods of type $X$, $Y$ or $G$) has auxiliary weight
--
--   $$w(B) = H = 17k^2$$
--
--   if and only if $B = \{G_h\}$ for some $h$ or $B = \{X_j, Y_j\}$ for some $j$ (a matched pair with the same index).
--
--   It forces every bundle containing a $Z$-good in a near-MMS allocation to carry exactly one $G$-good or one matched pair.
--
--   Differences from the source:
--   - encoding: a subset of the low goods of the instance → a finite set of values of the goods type Good k all of which are X, Y or G; reason: the low goods are exactly these values; same sets
-- source:
--   Ezra and Garbuz, Improved Impossibility Bounds for Maximin Share Allocations, 2026 preprint, STOC 2027 submission #115, SHA-256 8e8d63bbe3b0c850c561528c6e8d5bdb6da3bc426e5f64316cc948d5a31d64a6, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/115.pdf, Lemma 7, PDF p. 9 (printed p. 8)

import Mathlib
import Definitions.Def_MMSImpossibility_Goods_Instance

namespace MMSImpossibility.Goods

/-- Lemma 7 (PDF p. 9): for `n ≥ 2^16` and `k = 8⌈log₂ n⌉`, a set `B` of low goods (goods of
type `X`, `Y` or `G`) has auxiliary weight `H` if and only if it is a singleton `{G_h}` or a
matched pair `{X_j, Y_j}` with the same index. -/
theorem lemma_7 (n : ℕ) (hn : 2 ^ 16 ≤ n) (B : Finset (Good (kOf n)))
    (hB : ∀ g ∈ B, IsLow g) :
    ∑ g ∈ B, weight g = Hw (kOf n) ↔
      (∃ h, B = {Good.G h}) ∨ (∃ j, B = {Good.X j, Good.Y j}) := by sorry

end MMSImpossibility.Goods
