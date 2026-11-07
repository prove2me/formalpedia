-- Prove2me | Theorems.Thm_LosslessCond_theorem_5_4
-- name    : LosslessCond.theorem_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:33:52.628682+00:00
-- url     : https://prove2.me/theorems/69f4088c-8f75-412a-9b35-df5c65957031
-- title:
--   Theorem 5.4 — rank-sensitive condensation on a $2^{c-2}$-square
-- statement:
--   Let $M:X\times Y\to\{0,1\}$ be a finite Boolean matrix with $c=D(M)\ge 2$, let $r=\operatorname{rank}(M)$ over $\mathbb R$, and let $h=\lceil\log(r+1)\rceil$. Then $M$ contains an original $2^{c-2}\times 2^{c-2}$ submatrix $N$, on exactly $2^{c-2}$ distinct original rows and $2^{c-2}$ distinct original columns, with
--   $$
--   D(N)\ge c-2h-\lceil\log(h+1)\rceil-1.
--   $$
--
--   A matrix of small logarithmic rank thus has a square retaining nearly all of its depth; this is the low-rank case of Theorem 5.5 and of Corollary 1.2.
--
--   Differences from the source:
--   - encoding: the lower bound c − 2h − ⌈log(h + 1)⌉ − 1 → compared in ℤ; reason: the bound can be negative; the existence of the square is then the content
--   - encoding: D(M[U, V]) for the submatrix on U × V → DetCCHard.commCost M U V, the least depth of a protocol on all of X, Y correct on U × V; reason: protocols restrict and extend, so the two costs agree on every instance
--   - encoding: finite nonempty input sets X, Y → finite types X Y : Type (Fintype), nonemptiness not assumed; reason: every finite set is equivalent to a type in universe 0; where nonemptiness matters it is assumed or forced by the other hypotheses
-- source:
--   Mackenzie, Lossless Hardness Condensation in Deterministic Communication Complexity, arXiv:2609.28691 (held version, sha256 ce75e6d41cda6fdcdc55c619ab80e2b628e40845768cc3021cc0a0bfe7743fcf), Theorem 5.4, p.15 (PDF p.16)

import Mathlib
import Definitions.Def_DetCCHard_commCost
import Definitions.Def_DetCCHard_realRank

namespace LosslessCond

/-- **Theorem 5.4 (Rank-sensitive condensation)** (Mackenzie, *Lossless Hardness Condensation in
Deterministic Communication Complexity*, arXiv:2609.28691, held version sha256 ce75e6d4…, p.15).
Let `c = D(M) ≥ 2`, `r = rank(M)`, and `h = ⌈log(r + 1)⌉`. Then `M` contains an original
`2^(c−2)`-by-`2^(c−2)` submatrix `N` with `D(N) ≥ c − 2h − ⌈log(h + 1)⌉ − 1`.

**Formalization Note** `N = M[U, V]` for `Finset`s `U`, `V` of original labels with exactly
`2^(c−2)` elements each, and `D(N) = DetCCHard.commCost M U V`. The lower bound can be negative, so
it is compared in `ℤ`. `⌈log m⌉ = Nat.clog 2 m`. -/
theorem theorem_5_4 {X Y : Type} [Fintype X] [Fintype Y] (M : X → Y → Bool) (c : ℕ)
    (hc : DetCCHard.Dcost M = c) (hc2 : 2 ≤ c) :
    ∃ (U : Finset X) (V : Finset Y), U.card = 2 ^ (c - 2) ∧ V.card = 2 ^ (c - 2) ∧
      (c : ℤ) - 2 * (Nat.clog 2 (DetCCHard.realRank M + 1) : ℤ)
          - (Nat.clog 2 (Nat.clog 2 (DetCCHard.realRank M + 1) + 1) : ℤ) - 1 ≤
        (DetCCHard.commCost M (U : Set X) (V : Set Y) : ℤ) := by sorry

end LosslessCond
