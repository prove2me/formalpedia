-- Prove2me | Theorems.Thm_IsDiscreteValuationRing_exists_isDiscreteValuationRing_isFractionRing_faithfullyFlat_of_finiteDimensional
-- name    : IsDiscreteValuationRing.exists_isDiscreteValuationRing_isFractionRing_faithfullyFlat_of_finiteDimensional
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/14b0a382-3138-5e8a-9822-f82164750e01
-- title:
--   Faithfully flat DVR extension along a finite extension of fraction fields
-- statement:
--   Let $\mathcal O$ be a discrete valuation ring (a commutative domain that is a principal ideal ring and a local ring which is not a field), let $K$ be a field that is a fraction field of $\mathcal O$ via a given algebra structure, and let $K'$ be a field which is a finite-dimensional extension of $K$, equipped with an $\mathcal O$-algebra structure compatible with $\mathcal O \to K \to K'$. The conclusion asserts the existence of a type $\mathcal O'$ together with: a commutative ring structure making it a domain and a discrete valuation ring; an $\mathcal O$-algebra structure on $\mathcal O'$; an $\mathcal O'$-algebra structure on $K'$ compatible with the $\mathcal O$-algebra structures, i.e. $\mathcal O \to \mathcal O' \to K'$ is a tower; the property that $K'$ is a fraction field of $\mathcal O'$; the structure map $\mathcal O \to \mathcal O'$ is a local homomorphism (non-units are sent to non-units); and $\mathcal O'$ is faithfully flat as an $\mathcal O$-module. No separability, characteristic or residue-field hypothesis is imposed, and no control of the residue extension or of the ramification index is claimed.
--
--   This is the packaging, for consumers that work with an abstract base discrete valuation ring together with an identification of its fraction field, of the extension of a discrete valuation to a finite extension of its fraction field (Krull–Akizuki), with the additional assertions that the extension is local and faithfully flat. It is used in the reduction of a statement about square roots of polarisations to the case of a discrete valuation ring, via [`AlgebraicGeometry.Polarisation.exists_faithfullyFlat_principalSqrt_of_exists_faithfullyFlat_principalSqrt_pullback_of_isDiscreteValuationRing`](thm.html#AlgebraicGeometry.Polarisation.exists_faithfullyFlat_principalSqrt_of_exists_faithfullyFlat_principalSqrt_pullback_of_isDiscreteValuationRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDiscreteValuationRing_exists_isDiscreteValuationRing_isFractionRing_faithfullyFlat_of_finiteDimensional.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsDiscreteValuationRing.exists_isDiscreteValuationRing_isFractionRing_faithfullyFlat_of_finiteDimensional
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    (K : Type) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
    (K' : Type) [Field K'] [Algebra K K'] [FiniteDimensional K K'] [Algebra 𝒪 K'] [IsScalarTower 𝒪 K K'] :
    ∃ (𝒪' : Type) (_ : CommRing 𝒪') (_ : IsDomain 𝒪') (_ : IsDiscreteValuationRing 𝒪')
      (_ : Algebra 𝒪 𝒪') (_ : Algebra 𝒪' K') (_ : IsScalarTower 𝒪 𝒪' K') (_ : IsFractionRing 𝒪' K')
      (_ : IsLocalHom (algebraMap 𝒪 𝒪')), Module.FaithfullyFlat 𝒪 𝒪' := by sorry
