-- Prove2me | Theorems.Thm_NumberField_InfinitePlace_natCard_units_completion_quotient_range_powMonoidHom_of_isReal
-- name    : NumberField.InfinitePlace.natCard_units_completion_quotient_range_powMonoidHom_of_isReal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/65217925-6a2a-5c9c-82b2-f157ae6fdbe7
-- title:
--   Real place: index of n-th powers in K_w^×
-- statement:
--   Let $K$ be a field and let $w$ be an infinite place of $K$, i.e. a place arising from a complex embedding of $K$, and assume $w$ is real (`w.IsReal`, so $w$ comes from an embedding $K \to \mathbb{C}$ whose image lies in $\mathbb{R}$, equivalently one fixed by complex conjugation). Let $n$ be a natural number with $n > 0$. Consider the completion $K_w$ of $K$ at $w$, its group of units $K_w^\times$, and the monoid endomorphism $u \mapsto u^n$ of $K_w^\times$ given by `powMonoidHom n`; its range is a subgroup of $K_w^\times$, namely the subgroup $(K_w^\times)^n$ of $n$-th powers. The assertion is that the quotient group $K_w^\times / (K_w^\times)^n$ has cardinality (in the sense of `Nat.card`) equal to $2$ if $n$ is even and to $1$ if $n$ is odd. Since the quotient is finite here, this is the same as the statement that the index $[K_w^\times : (K_w^\times)^n]$ equals $2$ for even $n$ and $1$ for odd $n$.
--
--   This is the local count of $n$-th power classes at a real archimedean place: $\mathbb{R}^\times/(\mathbb{R}^\times)^n$ has order $2$ or $1$ according to the parity of $n$. It feeds into [`NumberField.prod_natCard_units_adicCompletion_quotient_range_powMonoidHom_mul_prod_infinitePlace_eq_pow`](thm.html#NumberField.prod_natCard_units_adicCompletion_quotient_range_powMonoidHom_mul_prod_infinitePlace_eq_pow), where the archimedean and non-archimedean local indices are multiplied together.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_InfinitePlace_natCard_units_completion_quotient_range_powMonoidHom_of_isReal.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem NumberField.InfinitePlace.natCard_units_completion_quotient_range_powMonoidHom_of_isReal {K : Type*} [Field K]
    (w : NumberField.InfinitePlace K) (hw : w.IsReal) {n : ℕ} (hn : 0 < n) :
    Nat.card ((w.Completion)ˣ ⧸ (powMonoidHom n : (w.Completion)ˣ →* (w.Completion)ˣ).range)
      = if Even n then 2 else 1 := by sorry
