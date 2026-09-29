-- Prove2me | Theorems.Thm_IsDiscreteValuationRing_exists_finite_extension_residueField_splits_quadratic
-- name    : IsDiscreteValuationRing.exists_finite_extension_residueField_splits_quadratic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/9079f4c6-d1d1-5c79-97b7-6ea219bb91f4
-- title:
--   Finite extension whose residue field splits quadratics
-- statement:
--   Let $\mathcal{O}$ be a commutative domain which is a discrete valuation ring, complete with respect to the adic topology of its maximal ideal, with finite residue field and of characteristic zero. Then there exists a ring $\mathcal{O}'$, again a commutative domain which is a discrete valuation ring, complete for its maximal-ideal-adic topology, with finite residue field and of characteristic zero, together with an $\mathcal{O}$-algebra structure on $\mathcal{O}'$ making $\mathcal{O}'$ a finite $\mathcal{O}$-module and making the structure map $\mathcal{O} \to \mathcal{O}'$ a local homomorphism (the preimage of the maximal ideal of $\mathcal{O}'$ is the maximal ideal of $\mathcal{O}$), such that two conditions hold: the structure map $\mathcal{O} \to \mathcal{O}'$ is injective; and for all $a, b$ in the residue field of $\mathcal{O}$ there are elements $x, y$ of the residue field of $\mathcal{O}'$ with the identity $z^2 - \bar{a} z + \bar{b} = (z-x)(z-y)$ holding for every $z$ in the residue field of $\mathcal{O}'$, where $\bar{a}, \bar{b}$ denote the images of $a, b$ under the induced map of residue fields. The factorisation is asserted as an identity of values at all $z$, not as an identity of polynomials.
--
--   This is the standard enlargement of the coefficient ring of a deformation problem by an unramified quadratic extension, so that the residue field becomes large enough to contain the eigenvalues of the residual representation at all relevant Frobenius elements. It is used in the construction of the patching data for the modularity lifting arguments at the primes $3$ and $5$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDiscreteValuationRing_exists_finite_extension_residueField_splits_quadratic.lean

import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Algebra.CharZero.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsDiscreteValuationRing.exists_finite_extension_residueField_splits_quadratic
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)] [CharZero 𝒪] :
    ∃ (𝒪' : Type) (_ : CommRing 𝒪') (_ : IsDomain 𝒪') (_ : IsDiscreteValuationRing 𝒪')
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal 𝒪') 𝒪')
      (_ : Finite (IsLocalRing.ResidueField 𝒪')) (_ : CharZero 𝒪')
      (_ : Algebra 𝒪 𝒪') (_ : Module.Finite 𝒪 𝒪') (_ : IsLocalHom (algebraMap 𝒪 𝒪')),
    Function.Injective (algebraMap 𝒪 𝒪') ∧
    ∀ a b : IsLocalRing.ResidueField 𝒪, ∃ x y : IsLocalRing.ResidueField 𝒪',
      ∀ z : IsLocalRing.ResidueField 𝒪',
        z ^ 2 - IsLocalRing.ResidueField.map (algebraMap 𝒪 𝒪') a * z + IsLocalRing.ResidueField.map (algebraMap 𝒪 𝒪') b =
          (z - x) * (z - y) := by sorry
