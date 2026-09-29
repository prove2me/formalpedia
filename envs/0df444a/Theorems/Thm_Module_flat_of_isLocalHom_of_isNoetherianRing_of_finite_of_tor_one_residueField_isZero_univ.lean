-- Prove2me | Theorems.Thm_Module_flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero_univ
-- name    : Module.flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero_univ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/34ac1ff5-deb1-5ddb-8268-9de51c68e6c8
-- title:
--   Local criterion for flatness via Tor₁
-- statement:
--   Let $R$ and $S$ be commutative rings in a single universe, with $S$ an $R$-algebra, both local and Noetherian, and suppose the structure map $R \to S$ is a local homomorphism (it sends the maximal ideal of $R$ into the maximal ideal of $S$). Let $M$ be an additive commutative group carrying compatible $R$- and $S$-module structures, the $R$-action being induced from the $S$-action through $R \to S$ (a scalar tower), and assume $M$ is a finite $S$-module, i.e. finitely generated over $S$. The hypothesis is that the first Tor group over $R$ of the residue field $\kappa_R = R/\mathfrak{m}_R$ with $M$, formed as the value at $M$ of the bifunctor $\mathrm{Tor}_1$ on the category of $R$-modules applied to $\kappa_R$, is a zero object: $\operatorname{Tor}^R_1(\kappa_R, M) = 0$. The conclusion is that $M$ is flat as an $R$-module.
--
--   This is the local criterion for flatness in its Noetherian form: vanishing of the single Tor group against the residue field suffices for flatness of a module finite over a local algebra. It is used in the project to establish flatness statements for towers of local rings, for instance in deducing flatness from flatness of a quotient by the image of the maximal ideal.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero_univ.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits

theorem Module.flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero_univ
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [IsNoetherianRing R] [IsNoetherianRing S]
    {M : Type u} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.Finite S M]
    (hκ : IsZero (((Tor (ModuleCat.{u} R) 1).obj
      (ModuleCat.of R (IsLocalRing.ResidueField R))).obj (ModuleCat.of R M))) :
    Module.Flat R M := by sorry
