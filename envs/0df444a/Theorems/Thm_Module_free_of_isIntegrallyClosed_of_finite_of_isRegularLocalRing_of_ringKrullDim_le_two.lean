-- Prove2me | Theorems.Thm_Module_free_of_isIntegrallyClosed_of_finite_of_isRegularLocalRing_of_ringKrullDim_le_two
-- name    : Module.free_of_isIntegrallyClosed_of_finite_of_isRegularLocalRing_of_ringKrullDim_le_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/2a46d48d-49c8-5089-b582-804580dadeb7
-- title:
--   Normal domains finite over regular local rings of dimension ≤ 2 are free
-- statement:
--   Let $R$ be a commutative ring which is a domain and a regular local ring, whose Krull dimension satisfies $\operatorname{ringKrullDim} R \le 2$ (the inequality being taken in the extended order on $\mathbb{Z}\cup\{\pm\infty\}$, so that it permits $\dim R\in\{0,1,2\}$). Let $B$ be a commutative ring, also a domain, integrally closed in its field of fractions, equipped with an $R$-algebra structure making $B$ a finite $R$-module, and such that the scalar action of $R$ on $B$ is faithful, i.e. the structure map $R \to B$ is injective. Both $R$ and $B$ are taken in the same universe. Under these hypotheses $B$ is a free $R$-module. No rank is asserted and no basis is produced; the conclusion is the bare existence of an $R$-basis of $B$, in the form of the `Module.Free R B` instance.
--
--   This is the two-dimensional case of the classical statement that a normal domain finite over a regular local ring of dimension at most two is free over it, obtained through reflexivity, maximal Cohen–Macaulayness and the Auslander–Buchsbaum formula. Within the project it supplies flatness-by-freeness at two-dimensional regular base points, and is used in the unramifiedness and regularity analysis of fibres of modular curves at full level, for instance by [`Algebra.existsUnique_prime_le_map_sup_span_eq_maximalIdeal_of_isUnramifiedAt_of_isDedekindDomain_quotient`](thm.html#Algebra.existsUnique_prime_le_map_sup_span_eq_maximalIdeal_of_isUnramifiedAt_of_isDedekindDomain_quotient) and by the regularity criteria for the fibre [`ModularCurve.FullLevel.isRegularLocalRing_fibre_of_forall_height_one_isUnramifiedAt_chartAlgInf_xH`](thm.html#ModularCurve.FullLevel.isRegularLocalRing_fibre_of_forall_height_one_isUnramifiedAt_chartAlgInf_xH).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_free_of_isIntegrallyClosed_of_finite_of_isRegularLocalRing_of_ringKrullDim_le_two.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem Module.free_of_isIntegrallyClosed_of_finite_of_isRegularLocalRing_of_ringKrullDim_le_two
    (R : Type u) [CommRing R] [IsDomain R] [IsRegularLocalRing R] (hdim : ringKrullDim R ≤ 2)
    (B : Type u) [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [Algebra R B] [Module.Finite R B]
    [FaithfulSMul R B] :
    Module.Free R B := by sorry
