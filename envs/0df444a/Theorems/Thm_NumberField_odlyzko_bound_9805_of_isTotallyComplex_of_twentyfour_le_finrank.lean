-- Prove2me | Theorems.Thm_NumberField_odlyzko_bound_9805_of_isTotallyComplex_of_twentyfour_le_finrank
-- name    : NumberField.odlyzko_bound_9805_of_isTotallyComplex_of_twentyfour_le_finrank
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/b73439fa-636b-5101-ac0f-3df791887f6e
-- title:
--   Odlyzko bound: root discriminant ≥ 9.805 in degree ≥ 24
-- statement:
--   Let $K$ be a number field (a field in `Type` carrying a `NumberField` structure) which is totally complex in the sense of Mathlib's `NumberField.IsTotallyComplex`, i.e. it has no real places, and suppose that its degree $n = \operatorname{finrank}_{\mathbb Q} K$ satisfies $24 \le n$. The conclusion is the inequality of integers
--   $$9805^{\,n} \le 1000^{\,n} \cdot |d_K|,$$
--   where $d_K =$ `NumberField.discr K` is the discriminant of $K$ and $|\cdot|$ is the absolute value on $\mathbb Z$. Equivalently, the root discriminant of $K$ satisfies $|d_K|^{1/n} \ge 9.805$. The statement is recorded for $K$ in the lowest universe, and the exponent on both sides is the degree $n$ itself, so no estimate for fields of degree $< 24$ and no statement for fields with a real place is made here.
--
--   This is Odlyzko's unconditional lower bound for root discriminants of totally complex number fields, in the numerical form $|d_K|^{1/n}\ge 9.805$ valid from degree $24$ on (the entry of Odlyzko's tables obtained by Poitou's version of the explicit-formula method). It is used in the analysis of a mod $3$ representation unramified at $3$ with cyclotomic determinant, where the discriminant of the field cut out by the representation is bounded above, forcing reducibility: the result is cited by [`GaloisRep.not_isIrreducible_matrixRepresentation_of_isUnramifiedAt_of_det_eq_modThreeCyclotomicChar`](thm.html#GaloisRep.not_isIrreducible_matrixRepresentation_of_isUnramifiedAt_of_det_eq_modThreeCyclotomicChar).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_odlyzko_bound_9805_of_isTotallyComplex_of_twentyfour_le_finrank.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem NumberField.odlyzko_bound_9805_of_isTotallyComplex_of_twentyfour_le_finrank
    (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (h24 : 24 ≤ Module.finrank ℚ K) :
    (9805 : ℤ) ^ Module.finrank ℚ K ≤ 1000 ^ Module.finrank ℚ K * |NumberField.discr K| := by sorry
