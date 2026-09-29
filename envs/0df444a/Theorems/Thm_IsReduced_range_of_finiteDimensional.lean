-- Prove2me | Theorems.Thm_IsReduced_range_of_finiteDimensional
-- name    : IsReduced.range_of_finiteDimensional
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/4abbdd35-7850-582f-a2ae-14f676a2d4dc
-- title:
--   Reducedness of the image of a reduced finite-dimensional algebra
-- statement:
--   Let $K$ be a field and let $A$ be a commutative $K$-algebra which is finite-dimensional as a $K$-vector space and reduced (its only nilpotent element is $0$). Let $B$ be a ring, not assumed commutative, equipped with a $K$-algebra structure, and let $f \colon A \to B$ be a homomorphism of $K$-algebras. The assertion is that the subalgebra $f.\mathrm{range} = f(A) \subseteq B$, viewed as a ring in its own right, is reduced: every element of $f(A)$ some power of which vanishes is itself $0$. Equivalently, for $a \in A$ and $n \in \mathbb{N}$ with $f(a)^n = 0$ in $B$ one has $f(a) = 0$. No finiteness, commutativity or reducedness hypothesis is imposed on $B$; the hypotheses on $A$ alone force the image to be reduced.
--
--   This is the standard fact that a reduced finite-dimensional commutative algebra over a field is semisimple — a finite product of fields — so that all of its quotients, in particular all of its homomorphic images inside an arbitrary ring, are again reduced; finite-dimensionality is essential, since quotients of general reduced rings need not be reduced. It is used to show that the rational Hecke algebra attached to a modular curve, realised as the image of a reduced finite-dimensional algebra acting on a space of modular forms, is reduced ([`ModularCurve.isReduced_rationalHeckeAlgebra`](thm.html#ModularCurve.isReduced_rationalHeckeAlgebra)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsReduced_range_of_finiteDimensional.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsReduced.range_of_finiteDimensional
    {K A B : Type*} [Field K] [CommRing A] [Algebra K A] [FiniteDimensional K A] [IsReduced A] [Ring B] [Algebra K B]
    (f : A →ₐ[K] B) : IsReduced ↥f.range := by sorry
