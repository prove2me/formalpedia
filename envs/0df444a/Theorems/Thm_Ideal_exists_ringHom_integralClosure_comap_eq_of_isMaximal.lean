-- Prove2me | Theorems.Thm_Ideal_exists_ringHom_integralClosure_comap_eq_of_isMaximal
-- name    : Ideal.exists_ringHom_integralClosure_comap_eq_of_isMaximal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/dea84553-3880-5909-984d-6aeb3c39fc84
-- title:
--   Maximal ideals of finite torsion-free ℤ-algebras lift to ℤ̄
-- statement:
--   Let $T$ be a commutative ring which is torsion-free as an additive group and finitely generated as a $\mathbb Z$-module, and let $\mathfrak m$ be an ideal of $T$ which is maximal. The assertion is that there exist a ring homomorphism $f \colon T \to \mathrm{integralClosure}\ \mathbb Z\ \mathbb C$, the ring of algebraic integers inside $\mathbb C$, and an ideal $\mathfrak M$ of that ring, such that $\mathfrak M$ is maximal and its preimage (contraction) along $f$ is exactly $\mathfrak m$, i.e. $f^{-1}(\mathfrak M) = \mathfrak m$. No compatibility of $f$ with any extra structure is required, and $f$ is not asserted to be injective or unique: only the existence of some homomorphism to $\overline{\mathbb Z}$ together with a maximal ideal above $\mathfrak m$ is claimed. In particular the residue field $T/\mathfrak m$ embeds into the residue field of $\mathfrak M$, which is an algebraic closure of a prime field or a number field's residue field according to the residue characteristic.
--
--   This is the commutative-algebra form of the Deligne–Serre lifting lemma: a system of Hecke eigenvalues in the residue field of a maximal ideal of a finite torsion-free $\mathbb Z$-algebra is the reduction of a system of algebraic-integer eigenvalues. It is used in [`WeierstrassCurve.isResiduallyModularOfLevel_iff_exists_ideal_heckeAlgebra`](thm.html#WeierstrassCurve.isResiduallyModularOfLevel_iff_exists_ideal_heckeAlgebra) to pass between maximal ideals of a Hecke algebra and eigenvalue systems with values in $\overline{\mathbb Z}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ideal_exists_ringHom_integralClosure_comap_eq_of_isMaximal.lean

import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Data.Complex.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Ideal.exists_ringHom_integralClosure_comap_eq_of_isMaximal {T : Type*} [CommRing T] [IsAddTorsionFree T] [Module.Finite ℤ T] (𝔪 : Ideal T) (h𝔪 : 𝔪.IsMaximal) : ∃ (f : T →+* integralClosure ℤ ℂ) (𝔐 : Ideal (integralClosure ℤ ℂ)), 𝔐.IsMaximal ∧ 𝔐.comap f = 𝔪 := by sorry
