-- Prove2me | Theorems.Thm_IntermediateField_finite_units_quotient_range_powMonoidHom_padic
-- name    : IntermediateField.finite_units_quotient_range_powMonoidHom_padic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/7213ba14-674d-5ba2-919c-29f834b9a2cc
-- title:
--   Finiteness of K^×/(K^×)ⁿ for K/ℚ_q finite
-- statement:
--   Let $q$ be a natural number carrying the hypothesis that it is prime, and let $K$ be an intermediate field of the extension $\mathbb{Q}_q \subseteq$ `PadicAlgCl q` (an algebraic closure of $\mathbb{Q}_q$) which is finite-dimensional over $\mathbb{Q}_q$. Let $n$ be a natural number with $0 < n$. The assertion is that the quotient group $K^\times / \mathrm{range}(\mathrm{powMonoidHom}\ n)$ is finite, where `powMonoidHom n` is the monoid endomorphism $x \mapsto x^n$ of the unit group $K^\times$ of $K$; since $K^\times$ is commutative, its range is exactly the subgroup $(K^\times)^n$ of $n$-th powers. Thus $K^\times/(K^\times)^n$ is a finite group. No bound on its order is asserted, only finiteness, and the conclusion is stated as a `Finite` instance on the quotient.
--
--   This is the standard local finiteness statement $\#\bigl(K^\times/(K^\times)^n\bigr) < \infty$ for a finite extension $K$ of $\mathbb{Q}_q$, the input that Kummer theory requires in order to bound continuous $H^1$ of the local Galois group with coefficients in $\mu_p$ or $\mathbb{F}_p$. It is used in the proof that the continuous $H^1$ of the fixing subgroup attached to a local place is finite-dimensional.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IntermediateField_finite_units_quotient_range_powMonoidHom_padic.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IntermediateField.finite_units_quotient_range_powMonoidHom_padic
    (q : ℕ) [Fact q.Prime] (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K]
    (n : ℕ) (hn : 0 < n) :
    Finite ((↥K)ˣ ⧸ (powMonoidHom n : (↥K)ˣ →* (↥K)ˣ).range) := by sorry
