-- Prove2me | Theorems.Thm_IsIntegrallyClosed_of_directed_iUnion_subring
-- name    : IsIntegrallyClosed.of_directed_iUnion_subring
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/d67ab989-5012-5ba9-acba-82ad1ee0405c
-- title:
--   Directed unions of integrally closed subrings are integrally closed
-- statement:
--   Let $B$ be a commutative ring which is a domain, let $\iota$ be a non-empty index type, and let $S : \iota \to \mathrm{Subring}\ B$ be a family of subrings of $B$. Assume: the family is directed for inclusion, i.e. for all $i, j$ there is $k$ with $S_i \le S_k$ and $S_j \le S_k$ (`Directed (· ≤ ·) S`); the family covers $B$, i.e. every $x \in B$ lies in some $S_i$; and each $S_i$, regarded as a ring in its own right, is integrally closed in the sense of Mathlib's `IsIntegrallyClosed`, namely every element of its fraction field that is integral over it lies in the image of $S_i$. The conclusion is that $B$ itself is integrally closed in this sense: every element of $\mathrm{Frac}(B)$ integral over $B$ comes from $B$. Note that the hypotheses do not assume the $S_i$ to be distinct or the index set to be a poset beyond the directedness condition; no Noetherian or finiteness assumption is imposed.
--
--   This is the standard fact that a filtered union (more generally a filtered colimit along injections) of normal domains is normal. It is used in the construction of integral models of modular curves, where a ring such as a valuation ring of $\overline{\mathbf{Q}}$ is exhibited as the directed union of its intersections with number fields, the relevant instances being invoked by the two `ModularCurve` statements on chart algebras after base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsIntegrallyClosed_of_directed_iUnion_subring.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

theorem IsIntegrallyClosed.of_directed_iUnion_subring
    {B : Type u} [CommRing B] [IsDomain B] {ι : Type v} [Nonempty ι] (S : ι → Subring B)
    (hdir : Directed (· ≤ ·) S) (hcov : ∀ x : B, ∃ i, x ∈ S i)
    (hS : ∀ i, IsIntegrallyClosed (S i)) :
    IsIntegrallyClosed B := by sorry
