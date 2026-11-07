-- Prove2me | Theorems.Thm_LosslessCond_lemma_4_3
-- name    : LosslessCond.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:36:01.434057+00:00
-- url     : https://prove2.me/theorems/179ef64e-a0ff-480e-a43f-755b54b72d9f
-- title:
--   Lemma 4.3 — rank-sensitive domain count $|C_s|\le 2^{B(r)2^s-1}$
-- statement:
--   Let $M:X\times Y\to\{0,1\}$ be a finite Boolean matrix with $\operatorname{rank}(M)\le r$ over $\mathbb R$, for an integer $r\ge 1$. Then for every integer $s\ge 0$,
--   $$
--   |C_s|\le 2^{B(r)2^s-1},\qquad B(r)=(r+1)\lceil\log(r+1)\rceil+2, \tag{4.3}
--   $$
--   where $C_s$ is the family of all depth-$s$ protocol domains $G_P(U)$, over all row sets $U$ and all partial protocols $P$.
--
--   The bound is independent of the sizes of $X$ and $Y$; it feeds the union bound of Lemma 5.1.
--
--   Differences from the source:
--   - encoding: |C_s| → Set.ncard (domainFamily M s); reason: C_s is finite for finite Y, so ncard is its true size
--   - generalization: finite nonempty input sets X, Y → finite types X Y : Type (Fintype), nonemptiness not assumed; reason: every finite nonempty set is equivalent to a type in universe 0, so every instance of the source is covered; the instances with an empty X or Y are additional, and there the statement holds trivially
-- source:
--   Mackenzie, Lossless Hardness Condensation in Deterministic Communication Complexity, arXiv:2609.28691 (held version, sha256 ce75e6d41cda6fdcdc55c619ab80e2b628e40845768cc3021cc0a0bfe7743fcf), Lemma 4.3, (4.3), p.12 (PDF p.13)

import Mathlib
import Definitions.Def_DetCCHard_realRank
import Definitions.Def_LosslessCond_domainFamily
import Definitions.Def_LosslessCond_B

namespace LosslessCond

/-- **Lemma 4.3 (Rank-sensitive domain count)** (Mackenzie, *Lossless Hardness Condensation in
Deterministic Communication Complexity*, arXiv:2609.28691, held version sha256 ce75e6d4…, p.12,
(4.3)). If `rank(M) ≤ r` with `r ≥ 1`, then for every integer `s ≥ 0`,
`|C_s| ≤ 2^(B(r)·2^s − 1)`, where `B(r) = (r + 1)⌈log(r + 1)⌉ + 2` (4.2).

**Formalization Note** `C_s` is `domainFamily M s`, a finite family since `Y` is finite, so
`Set.ncard` is its true size. `B(r)·2^s ≥ 4`, so the natural subtraction is exact. -/
theorem lemma_4_3 {X Y : Type} [Fintype X] [Fintype Y] (M : X → Y → Bool) (r : ℕ) (hr : 1 ≤ r)
    (hrank : DetCCHard.realRank M ≤ r) (s : ℕ) :
    (domainFamily M s).ncard ≤ 2 ^ (B r * 2 ^ s - 1) := by sorry

end LosslessCond
