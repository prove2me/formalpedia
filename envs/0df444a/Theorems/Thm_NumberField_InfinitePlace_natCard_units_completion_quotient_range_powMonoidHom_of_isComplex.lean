-- Prove2me | Theorems.Thm_NumberField_InfinitePlace_natCard_units_completion_quotient_range_powMonoidHom_of_isComplex
-- name    : NumberField.InfinitePlace.natCard_units_completion_quotient_range_powMonoidHom_of_isComplex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/a80209b9-b930-58d8-a467-519f9b178954
-- title:
--   Every element of a complex completion is an n-th power
-- statement:
--   Let $K$ be a field and let $w$ be an infinite place of $K$ which is complex, i.e. satisfies `w.IsComplex`. Let $n$ be a natural number with $0 < n$. Write $K_w$ for the completion `w.Completion` of $K$ at $w$ and consider the monoid endomorphism $u \mapsto u^n$ of the unit group $K_w^\times$, given by `powMonoidHom n`. The assertion is that the quotient group $K_w^\times / \mathrm{range}(u \mapsto u^n)$ has cardinality $1$ as a natural number, i.e. `Nat.card` of this quotient equals $1$. Equivalently, the subgroup of $n$-th powers is the whole of $K_w^\times$: every nonzero element of $K_w$ is an $n$-th power, and the index $[K_w^\times : (K_w^\times)^n]$ equals $1$. No arithmetic hypothesis on $K$ beyond its being a field is imposed; in particular $K$ is not assumed to be a number field.
--
--   This is the index computation for $n$-th power classes at a complex archimedean place, the companion of the corresponding count at a real place (index $2$ for even $n$, $1$ for odd $n$) and at a finite place. It supplies the archimedean factor in [`NumberField.prod_natCard_units_adicCompletion_quotient_range_powMonoidHom_mul_prod_infinitePlace_eq_pow`](thm.html#NumberField.prod_natCard_units_adicCompletion_quotient_range_powMonoidHom_mul_prod_infinitePlace_eq_pow), the product formula for local $n$-th power indices over a finite set of places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_InfinitePlace_natCard_units_completion_quotient_range_powMonoidHom_of_isComplex.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem NumberField.InfinitePlace.natCard_units_completion_quotient_range_powMonoidHom_of_isComplex {K : Type*} [Field K]
    (w : NumberField.InfinitePlace K) (hw : w.IsComplex) {n : ℕ} (hn : 0 < n) :
    Nat.card ((w.Completion)ˣ ⧸ (powMonoidHom n : (w.Completion)ˣ →* (w.Completion)ˣ).range) = 1 := by sorry
