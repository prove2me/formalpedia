-- Prove2me | Theorems.Thm_IsLocalRing_etale_of_finite_of_finrank_eq_finrank_residueField
-- name    : IsLocalRing.etale_of_finite_of_finrank_eq_finrank_residueField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/a02f1d8c-fc7b-527f-ae02-921d49efc449
-- title:
--   Étale by count for finite local extensions of local domains
-- statement:
--   Let $O$ and $C$ be Noetherian local domains, with $C$ an $O$-algebra that is finite as an $O$-module, such that the structure map $O \to C$ is injective (the `FaithfulSMul` hypothesis) and local, i.e. carries the maximal ideal of $O$ into that of $C$. Assume: the $\mathfrak m_O$-adic completion $\widehat O$ is a domain and is integrally closed, the $\mathfrak m_C$-adic completion $\widehat C$ is a domain, and the residue field extension $\kappa(C)/\kappa(O)$ is separable. Let $K_1$ be a field realised as a fraction field of $O$ and $K$ a field realised as a fraction field of $C$, with $K$ a $K_1$-algebra and an $O$-algebra, compatibly in the sense that $O \to C \to K$ and $O \to K_1 \to K$ are towers of scalars. Assume finally the numerical equality $[K:K_1] = [\kappa(C):\kappa(O)]$ of the $K_1$-dimension of $K$ and the $\kappa(O)$-dimension of $\kappa(C)$. Then $C$ is étale as an $O$-algebra, i.e. `Algebra.Etale O C` holds (formally smooth and of finite presentation over $O$).
--
--   This is the purity-free "étale by count" criterion: for a module-finite local extension of analytically irreducible Noetherian local domains with separable residue extension, equality of the generic degree with the residue degree already forces étaleness. It is used in the analysis of the local structure of stable models at supersingular points, entering the construction of a subalgebra of fixed points of inertia that is étale over the base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_etale_of_finite_of_finrank_eq_finrank_residueField.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsLocalRing.etale_of_finite_of_finrank_eq_finrank_residueField
    {O C : Type*} [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsLocalRing O]
    [CommRing C] [IsDomain C] [IsNoetherianRing C] [IsLocalRing C]
    [Algebra O C] [Module.Finite O C] [FaithfulSMul O C] [IsLocalHom (algebraMap O C)]
    (hO : IsDomain (AdicCompletion (IsLocalRing.maximalIdeal O) O) ∧
      IsIntegrallyClosed (AdicCompletion (IsLocalRing.maximalIdeal O) O))
    (hC : IsDomain (AdicCompletion (IsLocalRing.maximalIdeal C) C))
    (K₁ K : Type*) [Field K₁] [Field K] [Algebra O K₁] [IsFractionRing O K₁]
    [Algebra C K] [IsFractionRing C K] [Algebra K₁ K] [Algebra O K]
    [IsScalarTower O C K] [IsScalarTower O K₁ K]
    [Algebra.IsSeparable (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField C)]
    (hcount : Module.finrank K₁ K =
      Module.finrank (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField C)) :
    Algebra.Etale O C := by sorry
