-- Prove2me | Theorems.Thm_M4aHerbrand_finrank_sUnit_eq_univ
-- name    : M4aHerbrand.finrank_sUnit_eq_univ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/91f441f2-166b-5dc5-bdd3-3190d9276343
-- title:
--   Dirichlet's S-unit theorem: the rank of 𝒪_{K,S}^×
-- statement:
--   Let $K$ be a field in an arbitrary universe, equipped with a number field structure, and let $S$ be a finite set of height one primes of the ring of integers $\mathcal{O}_K$, i.e. a finite subset of `HeightOneSpectrum (𝓞 K)`. The assertion is the conjunction of two statements about the group `S.unit K` of units of the ring of $S$-integers of $K$ — the elements $x \in K^\times$ whose valuation $v(x)$ is nonnegative for every height one prime $v \notin S$, so that the unit group consists of the $x \in K^\times$ with $v(x) = 0$ for all such $v$ — viewed additively as a $\mathbb{Z}$-module via `Additive`. First, this $\mathbb{Z}$-module is finitely generated, i.e. $\mathcal{O}_{K,S}^\times$ is a finitely generated abelian group. Second, its $\mathbb{Z}$-rank, `Module.finrank ℤ`, equals $\#S + \operatorname{rank} \mathcal{O}_K^\times$, where $\#S$ is the cardinality of $S$ as a natural number and `NumberField.Units.rank K` is Dirichlet's unit rank $r_1 + r_2 - 1$. Nothing is asserted about the torsion subgroup, nor is any system of fundamental $S$-units produced.
--
--   This is Dirichlet's $S$-unit theorem in the form of a rank computation, stated for number fields in an arbitrary universe. It is used in the computation of the cardinality of the quotient of the $S$-unit group by the image of the $n$-th power map, in [`NumberField.natCard_sUnit_quotient_range_powMonoidHom`](thm.html#NumberField.natCard_sUnit_quotient_range_powMonoidHom).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_finrank_sUnit_eq_univ.lean

import Mathlib.RingTheory.DedekindDomain.SInteger
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IsDedekindDomain NumberField

theorem M4aHerbrand.finrank_sUnit_eq_univ (K : Type*) [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S] :
    Module.Finite ℤ (Additive (S.unit K)) ∧
    Module.finrank ℤ (Additive (S.unit K)) = Nat.card S + NumberField.Units.rank K := by sorry
