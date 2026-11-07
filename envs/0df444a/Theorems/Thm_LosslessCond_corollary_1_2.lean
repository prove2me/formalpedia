-- Prove2me | Theorems.Thm_LosslessCond_corollary_1_2
-- name    : LosslessCond.corollary_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:33:55.346015+00:00
-- url     : https://prove2.me/theorems/cd44f370-9a5f-45e6-99b3-0fbe08c690fb
-- title:
--   Corollary 1.2 — an original $2^{c-2}$-square with $D(N)\ge(c-\lceil\log(c+1)\rceil-1)/3$
-- statement:
--   Let $M:X\times Y\to\{0,1\}$ be a finite total Boolean matrix with $D(M)=c\ge 4$. There is an original $2^{c-2}\times 2^{c-2}$ submatrix $N$, on exactly $2^{c-2}$ distinct original rows and $2^{c-2}$ distinct original columns, such that
--   $$
--   D(N)\ge\frac{c-\lceil\log(c+1)\rceil-1}{3}.
--   $$
--
--   At input length $c-2$ per player, one third of the original communication complexity survives up to an $O(\log c)$ loss. It combines the nonsingular-minor case of Lemma 4.1 with Theorem 5.4.
--
--   Differences from the source:
--   - encoding: the real lower bound (c − ⌈log(c + 1)⌉ − 1)/3 → compared in ℝ with casts; reason: same inequality
--   - encoding: D(M[U, V]) for the submatrix on U × V → DetCCHard.commCost M U V, the least depth of a protocol on all of X, Y correct on U × V; reason: protocols restrict and extend, so the two costs agree on every instance
--   - encoding: finite nonempty input sets X, Y → finite types X Y : Type (Fintype), nonemptiness not assumed; reason: every finite set is equivalent to a type in universe 0; where nonemptiness matters it is assumed or forced by the other hypotheses
-- source:
--   Mackenzie, Lossless Hardness Condensation in Deterministic Communication Complexity, arXiv:2609.28691 (held version, sha256 ce75e6d41cda6fdcdc55c619ab80e2b628e40845768cc3021cc0a0bfe7743fcf), Corollary 1.2, p.2 (PDF p.3); proof p.16 (PDF p.17)

import Mathlib
import Definitions.Def_DetCCHard_commCost

namespace LosslessCond

/-- **Corollary 1.2 (Retaining original complexity)** (Mackenzie, *Lossless Hardness Condensation
in Deterministic Communication Complexity*, arXiv:2609.28691, held version sha256 ce75e6d4…, p.2).
Let `M` be a finite total Boolean matrix with `D(M) = c ≥ 4`. There is an original
`2^(c−2)`-by-`2^(c−2)` submatrix `N` such that `D(N) ≥ (c − ⌈log(c + 1)⌉ − 1)/3`.

**Formalization Note** `N = M[U, V]` for `Finset`s `U`, `V` of original labels with exactly
`2^(c−2)` elements each, and `D(N) = DetCCHard.commCost M U V`. The bound is compared in `ℝ`;
`⌈log m⌉ = Nat.clog 2 m`. Finite input sets are `Fintype`s; `c ≥ 4` forces them to be nonempty. -/
theorem corollary_1_2 {X Y : Type} [Fintype X] [Fintype Y] (M : X → Y → Bool) (c : ℕ)
    (hc : DetCCHard.Dcost M = c) (hc4 : 4 ≤ c) :
    ∃ (U : Finset X) (V : Finset Y), U.card = 2 ^ (c - 2) ∧ V.card = 2 ^ (c - 2) ∧
      ((c : ℝ) - Nat.clog 2 (c + 1) - 1) / 3 ≤
        (DetCCHard.commCost M (U : Set X) (V : Set Y) : ℝ) := by sorry

end LosslessCond
