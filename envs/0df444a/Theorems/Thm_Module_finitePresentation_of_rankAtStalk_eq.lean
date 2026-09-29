-- Prove2me | Theorems.Thm_Module_finitePresentation_of_rankAtStalk_eq
-- name    : Module.finitePresentation_of_rankAtStalk_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/dfb07f6b-e088-5c20-91b8-adb9202472e3
-- title:
--   Finite flat modules of constant stalk rank are finitely presented
-- statement:
--   Let $R$ be a commutative ring and let $M$ be an $R$-module which is module-finite over $R$ and flat over $R$. Let $n$ be a natural number, and suppose that the rank of $M$ at every stalk equals $n$: for every prime $\mathfrak p$ of $R$ (i.e. every point of `PrimeSpectrum R`), the invariant `Module.rankAtStalk M p`, the rank of the localisation $M_{\mathfrak p}$ as a module over $R_{\mathfrak p}$, is equal to $n$. The conclusion is that $M$ is a finitely presented $R$-module, that is, $M$ is the quotient of a finite free $R$-module by a finitely generated submodule. Note that flatness and finiteness are hypotheses on $M$, while the constancy of the rank is imposed as equality with one fixed natural number $n$ at all primes simultaneously, not merely local constancy of the rank function; in particular the case of the zero ring, where $\operatorname{Spec} R$ is empty, is covered vacuously. Combined with finiteness and flatness, the conclusion upgrades $M$ to a finite projective, hence finite locally free, $R$-module.
--
--   This is the standard criterion that a finite flat module whose rank is constant on the prime spectrum is finitely presented, and therefore finite locally free of that rank. It is used in the project to recognise modules of sections as projective and in the construction of relative effective Cartier divisors, where an ideal must be identified with a locally free module of known rank.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_finitePresentation_of_rankAtStalk_eq.lean

import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem Module.finitePresentation_of_rankAtStalk_eq {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Flat R M] (n : ℕ)
    (h : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = n) : Module.FinitePresentation R M := by sorry
