-- Prove2me | Theorems.Thm_Module_Flat_of_finite_of_isLocalHom_of_isRegularLocalRing_of_ringKrullDim_eq
-- name    : Module.Flat.of_finite_of_isLocalHom_of_isRegularLocalRing_of_ringKrullDim_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/61378d52-d3c5-5f2e-8d73-3c05c1a889e8
-- title:
--   Miracle flatness for finite local maps of regular local rings
-- statement:
--   Let $R$ and $S$ be commutative rings, with $R$ Noetherian, both $R$ and $S$ regular local rings, and let $S$ be an $R$-algebra whose structure map $R \to S$ is a local homomorphism (it carries the maximal ideal of $R$ into the maximal ideal of $S$) making $S$ a finitely generated $R$-module. Assume furthermore that the Krull dimensions agree, $\operatorname{ringKrullDim} S = \operatorname{ringKrullDim} R$ as elements of $\mathrm{WithBot}\ \mathbb{N}_\infty$. The conclusion is that $S$ is flat as an $R$-module. Note that the dimension hypothesis is an equality of dimensions of the two rings, not a fibre-dimension condition, and that both rings are assumed regular rather than merely one regular and the other Cohen–Macaulay; the conclusion recorded is flatness, although the proof in fact produces freeness of $S$ over $R$.
--
--   This is the ring-theoretic form of miracle flatness: a module-finite local extension of regular local rings of equal dimension is flat (indeed free). It is used in the project for the flatness of finite extensions arising in the study of formal groups and power series algebras, being cited by [`MvFormalGroup.exists_forall_existsUnique_eq_sum_subst_nthSeries_mul_of_finrank_eq_pow`](thm.html#MvFormalGroup.exists_forall_existsUnique_eq_sum_subst_nthSeries_mul_of_finrank_eq_pow) and [`MvPowerSeries.finite_flat_exists_basis_substAlgHom_of_finite_quotient`](thm.html#MvPowerSeries.finite_flat_exists_basis_substAlgHom_of_finite_quotient).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_Flat_of_finite_of_isLocalHom_of_isRegularLocalRing_of_ringKrullDim_eq.lean

import Mathlib
import Definitions.Def_Patching_SystemTypes

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing RingTheory

theorem Module.Flat.of_finite_of_isLocalHom_of_isRegularLocalRing_of_ringKrullDim_eq
    (R S : Type*) [CommRing R] [CommRing S] [IsNoetherianRing R]
    [IsRegularLocalRing R] [IsRegularLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Module.Finite R S]
    (hdim : ringKrullDim S = ringKrullDim R) :
    Module.Flat R S := by sorry
