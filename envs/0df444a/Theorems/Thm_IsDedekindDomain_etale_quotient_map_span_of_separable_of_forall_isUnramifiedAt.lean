-- Prove2me | Theorems.Thm_IsDedekindDomain_etale_quotient_map_span_of_separable_of_forall_isUnramifiedAt
-- name    : IsDedekindDomain.etale_quotient_map_span_of_separable_of_forall_isUnramifiedAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/7939e536-bd74-5cd3-9050-e8900badd12a
-- title:
--   Étale quotient by a separable polynomial over a Dedekind domain
-- statement:
--   Let $k$ be a field and let $B$ be a commutative ring that is a Dedekind domain, equipped with an algebra structure over the polynomial ring $k[X]$ and over $k$ in a compatible way (the scalar tower $k \to k[X] \to B$), such that $B$ is a finite $k[X]$-module and has no zero smul divisors over $k[X]$, i.e. is torsion-free over $k[X]$; $k$ and $B$ lie in the same universe. Let $h \in k[X]$ be a separable polynomial, and assume that for every prime ideal $P$ of $B$ with $P \neq \bot$ whose contraction along $\mathrm{algebraMap}\ k[X]\ B$ contains the ideal $(h)$ — that is, every nonzero prime of $B$ lying over a prime of $k[X]$ containing $h$ — the algebra $B$ over $k[X]$ is unramified at $P$ in the sense of `Algebra.IsUnramifiedAt k[X] P`. The conclusion is that the quotient $B / h B$, where $hB$ denotes the image ideal $\mathrm{Ideal.map}$ of the span of $\{h\}$ under $\mathrm{algebraMap}\ k[X]\ B$, is an étale $k$-algebra.
--
--   This is the separable (not necessarily irreducible) case of the statement that the fibre of $\operatorname{Spec} B \to \operatorname{Spec} k[X]$ over the closed subscheme cut out by $h$ is étale over $k$ when the relevant primes of $B$ are unramified; it removes the irreducibility hypothesis from the companion result [`IsDedekindDomain.etale_quotient_map_span_of_forall_isUnramifiedAt`](thm.html#IsDedekindDomain.etale_quotient_map_span_of_forall_isUnramifiedAt). It is used in the construction of level rings attached to the $j$-line, in [`ModularCurve.HpoolLevelRing.exists_finite_etale_levelRing_self`](thm.html#ModularCurve.HpoolLevelRing.exists_finite_etale_levelRing_self) and [`ModularCurve.HpoolLevelRing.exists_forall_etale_zmod_tensorProduct_quotient_span_aeval_jChartFin`](thm.html#ModularCurve.HpoolLevelRing.exists_forall_etale_zmod_tensorProduct_quotient_span_aeval_jChartFin).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDedekindDomain_etale_quotient_map_span_of_separable_of_forall_isUnramifiedAt.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial TensorProduct

universe u

theorem IsDedekindDomain.etale_quotient_map_span_of_separable_of_forall_isUnramifiedAt
    {k : Type u} [Field k] (B : Type u) [CommRing B] [IsDedekindDomain B]
    [Algebra k[X] B] [Algebra k B] [IsScalarTower k k[X] B] [Module.Finite k[X] B] [NoZeroSMulDivisors k[X] B]
    (h : k[X]) (hsep : h.Separable)
    (hunr : ∀ (P : Ideal B) [P.IsPrime], P ≠ ⊥ → Ideal.span {h} ≤ P.comap (algebraMap k[X] B) →
      Algebra.IsUnramifiedAt k[X] P) :
    Algebra.Etale k (B ⧸ Ideal.map (algebraMap k[X] B) (Ideal.span {h})) := by sorry
