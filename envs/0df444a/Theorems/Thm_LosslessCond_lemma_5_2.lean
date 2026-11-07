-- Prove2me | Theorems.Thm_LosslessCond_lemma_5_2
-- name    : LosslessCond.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:34:26.775901+00:00
-- url     : https://prove2.me/theorems/95e16753-2fdf-467e-b0d7-d1a14648835c
-- title:
--   Lemma 5.2 — a cover by protocols: local easiness gives $D(M)\le s+\lceil\log r\rceil$
-- statement:
--   Let $M:X\times Y\to\{0,1\}$ be a finite Boolean matrix with $\operatorname{rank}(M)\le r$ for an integer $r\ge 1$, and let $s\ge 0$. If every nonempty column set $C\subseteq Y$ with $|C|\le a(r,s)$ satisfies $D(M[X,C])\le s$, then
--   $$
--   D(M)\le s+\lceil\log r\rceil. \tag{5.2}
--   $$
--
--   Its contrapositive produces a small column set on which $M$ stays hard, which is the first step of Lemma 5.3.
--
--   Differences from the source:
--   - encoding: D(M[U, V]) for the submatrix on U × V → DetCCHard.commCost M U V, the least depth of a protocol on all of X, Y correct on U × V; reason: protocols restrict and extend, so the two costs agree on every instance
--   - encoding: ⌈log r⌉ (base two) → Nat.clog 2 r; reason: equal for r ≥ 1
--   - generalization: finite nonempty input sets X, Y → finite types X Y : Type (Fintype), nonemptiness not assumed; reason: every finite nonempty set is equivalent to a type in universe 0, so every instance of the source is covered; the instances with an empty X or Y are additional, and there the statement holds trivially
-- source:
--   Mackenzie, Lossless Hardness Condensation in Deterministic Communication Complexity, arXiv:2609.28691 (held version, sha256 ce75e6d41cda6fdcdc55c619ab80e2b628e40845768cc3021cc0a0bfe7743fcf), Lemma 5.2, (5.2), p.13 (PDF p.14)

import Mathlib
import Definitions.Def_DetCCHard_commCost
import Definitions.Def_DetCCHard_realRank
import Definitions.Def_LosslessCond_B

namespace LosslessCond

/-- **Lemma 5.2 (A cover by protocols)** (Mackenzie, *Lossless Hardness Condensation in
Deterministic Communication Complexity*, arXiv:2609.28691, held version sha256 ce75e6d4…, p.13,
(5.2)). Suppose `rank(M) ≤ r` for an integer `r ≥ 1`. If every nonempty column set `C` with
`|C| ≤ a(r, s)` satisfies `D(M[X, C]) ≤ s`, then `D(M) ≤ s + ⌈log r⌉`.

**Formalization Note** `D(M[X, C])` is `DetCCHard.commCost M univ C`, `D(M)` is
`DetCCHard.Dcost M`, and `⌈log r⌉ = Nat.clog 2 r` (base two, exact for `r ≥ 1`). -/
theorem lemma_5_2 {X Y : Type} [Fintype X] [Fintype Y] (M : X → Y → Bool) (r : ℕ) (hr : 1 ≤ r)
    (hrank : DetCCHard.realRank M ≤ r) (s : ℕ)
    (hloc : ∀ C : Finset Y, C.Nonempty → C.card ≤ a r s →
      DetCCHard.commCost M Set.univ (C : Set Y) ≤ s) :
    DetCCHard.Dcost M ≤ s + Nat.clog 2 r := by sorry

end LosslessCond
