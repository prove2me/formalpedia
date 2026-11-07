-- Prove2me | Theorems.Thm_LosslessCond_eq_2_1
-- name    : LosslessCond.eq_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:33:36.72193+00:00
-- url     : https://prove2.me/theorems/8acb9772-f9f4-4b1d-8b50-449ce4560700
-- title:
--   (2.1) — restriction cannot increase, enlargement cannot decrease $D$
-- statement:
--   Let $M:X\times Y\to\{0,1\}$ be a finite Boolean matrix and write $D(M[U,V])$ for the deterministic communication complexity of the submatrix on rows $U$ and columns $V$. If $U\subseteq U'\subseteq X$ and $V\subseteq V'\subseteq Y$, then
--   $$
--   D(M[U,V])\le D(M[U',V']).
--   $$
--   With $U'=X$, $V'=Y$ this is $D(M[U,V])\le D(M)$ (2.1); read the other way, enlarging a hard submatrix with further original inputs cannot make it easier.
--
--   This monotonicity is used whenever a selected square is padded with unused original labels to reach an exact size (Theorem 5.4, Corollary 1.2).
--
--   Differences from the source:
--   - generalization: (2.1) for U' = X, V' = Y, and the enlargement remark, for nonempty U, V → monotonicity for all U ⊆ U', V ⊆ V', empty sets allowed; reason: (2.1) is the case U' = X, V' = Y and the enlargement remark is the general case; an empty U or V has cost 0, so the extra cases are trivially true
--   - encoding: D(M[U, V]) for the submatrix on U × V → DetCCHard.commCost M U V, the least depth of a protocol on all of X, Y correct on U × V; reason: protocols restrict and extend, so the two costs agree on every instance
--   - encoding: finite nonempty input sets X, Y → finite types X Y : Type (Fintype), nonemptiness not assumed; reason: every finite set is equivalent to a type in universe 0; where nonemptiness matters it is assumed or forced by the other hypotheses
-- source:
--   Mackenzie, Lossless Hardness Condensation in Deterministic Communication Complexity, arXiv:2609.28691 (held version, sha256 ce75e6d41cda6fdcdc55c619ab80e2b628e40845768cc3021cc0a0bfe7743fcf), (2.1) and the following sentence, §2, p.7 (PDF p.8)

import Mathlib
import Definitions.Def_DetCCHard_commCost

namespace LosslessCond

/-- **(2.1) and enlargement** (Mackenzie, *Lossless Hardness Condensation in Deterministic
Communication Complexity*, arXiv:2609.28691, held version sha256 ce75e6d4…, §2, p.7): restricting a
correct protocol gives `D(M[U, V]) ≤ D(M)`, and, in the reverse perspective, enlarging a submatrix
with additional original inputs cannot make it easier: if `U ⊆ U'` and `V ⊆ V'` then
`D(M[U, V]) ≤ D(M[U', V'])`.

**Formalization Note** `D(M[U, V])` is `DetCCHard.commCost M U V`, the least depth of a protocol
correct on `U × V`. (2.1) is the case `U' = X`, `V' = Y` (`commCost M univ univ = Dcost M`). -/
theorem eq_2_1 {X Y : Type} [Fintype X] [Fintype Y] (M : X → Y → Bool)
    (U U' : Set X) (V V' : Set Y) (hU : U ⊆ U') (hV : V ⊆ V') :
    DetCCHard.commCost M U V ≤ DetCCHard.commCost M U' V' := by sorry

end LosslessCond
