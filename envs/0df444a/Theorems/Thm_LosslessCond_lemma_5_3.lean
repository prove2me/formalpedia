-- Prove2me | Theorems.Thm_LosslessCond_lemma_5_3
-- name    : LosslessCond.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:34:11.294504+00:00
-- url     : https://prove2.me/theorems/625f3460-8927-4b10-8d7c-d7011169e19a
-- title:
--   Lemma 5.3 — a two-sided restriction with $D>s$, $|U|\le a(r,s)$, $|V|\le a(r,s+H)$
-- statement:
--   Let $M:X\times Y\to\{0,1\}$ be a finite Boolean matrix with $\operatorname{rank}(M)\le r$, $r\ge 1$. Let $H$ be any integer with $H\ge\lceil\log r\rceil$ and let $s\ge 0$. If $D(M)>s+2H$, then $M$ has an original submatrix $M[U,V]$ with
--   $$
--   D(M[U,V])>s,\qquad |U|\le a(r,s),\qquad |V|\le a(r,s+H). \tag{5.3}
--   $$
--   In particular this holds with $H=\lceil\log(r+1)\rceil$.
--
--   Lemma 5.3 restricts columns and then rows, paying the cover index once in each orientation; Theorem 5.4 applies it with $H=\lceil\log(r+1)\rceil$.
--
--   Differences from the source:
--   - encoding: an integer H ≥ ⌈log r⌉ → H : ℕ with Nat.clog 2 r ≤ H; reason: ⌈log r⌉ ≥ 0, so every admissible H is a natural number
--   - encoding: the "in particular" clause H = ⌈log(r + 1)⌉ → covered by the universally quantified H; reason: ⌈log(r + 1)⌉ ≥ ⌈log r⌉, so it is an instance
--   - encoding: D(M[U, V]) for the submatrix on U × V → DetCCHard.commCost M U V, the least depth of a protocol on all of X, Y correct on U × V; reason: protocols restrict and extend, so the two costs agree on every instance
--   - encoding: finite nonempty input sets X, Y → finite types X Y : Type (Fintype), nonemptiness not assumed; reason: every finite set is equivalent to a type in universe 0; where nonemptiness matters it is assumed or forced by the other hypotheses
-- source:
--   Mackenzie, Lossless Hardness Condensation in Deterministic Communication Complexity, arXiv:2609.28691 (held version, sha256 ce75e6d41cda6fdcdc55c619ab80e2b628e40845768cc3021cc0a0bfe7743fcf), Lemma 5.3, (5.3), p.14 (PDF p.15)

import Mathlib
import Definitions.Def_DetCCHard_commCost
import Definitions.Def_DetCCHard_realRank
import Definitions.Def_LosslessCond_B

namespace LosslessCond

/-- **Lemma 5.3 (A two-sided restriction)** (Mackenzie, *Lossless Hardness Condensation in
Deterministic Communication Complexity*, arXiv:2609.28691, held version sha256 ce75e6d4…, p.14,
(5.3)). Let `rank(M) ≤ r` with `r ≥ 1`. Let `H` be any integer with `H ≥ ⌈log r⌉`, and let `s ≥ 0`.
If `D(M) > s + 2H`, then `M` has an original submatrix `M[U, V]` such that
`D(M[U, V]) > s`, `|U| ≤ a(r, s)`, `|V| ≤ a(r, s + H)`.
In particular, this holds with `H = ⌈log(r + 1)⌉`.

**Formalization Note** `H` ranges over `ℕ`, which loses nothing since `H ≥ ⌈log r⌉ ≥ 0`. The
"in particular" clause is the instance `H = Nat.clog 2 (r + 1)`. `U` and `V` are `Finset`s of
original labels; they are nonempty because the cost exceeds `s ≥ 0`. -/
theorem lemma_5_3 {X Y : Type} [Fintype X] [Fintype Y] (M : X → Y → Bool) (r : ℕ) (hr : 1 ≤ r)
    (hrank : DetCCHard.realRank M ≤ r) (H : ℕ) (hH : Nat.clog 2 r ≤ H) (s : ℕ)
    (hD : s + 2 * H < DetCCHard.Dcost M) :
    ∃ (U : Finset X) (V : Finset Y), s < DetCCHard.commCost M (U : Set X) (V : Set Y) ∧
      U.card ≤ a r s ∧ V.card ≤ a r (s + H) := by sorry

end LosslessCond
