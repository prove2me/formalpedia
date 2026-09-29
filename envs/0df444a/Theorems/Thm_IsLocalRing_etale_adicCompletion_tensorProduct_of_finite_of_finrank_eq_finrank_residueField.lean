-- Prove2me | Theorems.Thm_IsLocalRing_etale_adicCompletion_tensorProduct_of_finite_of_finrank_eq_finrank_residueField
-- name    : IsLocalRing.etale_adicCompletion_tensorProduct_of_finite_of_finrank_eq_finrank_residueField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/d125d69f-799b-5047-a42c-fd242a42b055
-- title:
--   Étaleness of widehat O⊗_O C over widehat O by degree count
-- statement:
--   Let $O$ and $C$ be Noetherian local domains, with $C$ an $O$-algebra that is finite as an $O$-module, whose structure map $O \to C$ is injective (`FaithfulSMul`) and local. Write $\widehat O =$ `AdicCompletion (maximalIdeal O) O` for the adic completion of $O$ along its maximal ideal, and likewise $\widehat C$. Assume: $\widehat O$ is a domain and is integrally closed; $\widehat C$ is a domain; $K_1$ and $K$ are fields that are fraction fields of $O$ and of $C$ respectively, equipped with algebra structures making $O \to C \to K$ and $O \to K_1 \to K$ compatible towers; the residue field extension $\kappa(C)/\kappa(O)$, i.e. `ResidueField C` over `ResidueField O`, is separable; and the degrees match, $[K : K_1] = [\kappa(C) : \kappa(O)]$ as `Module.finrank`. The conclusion is that the $\widehat O$-algebra $\widehat O \otimes_O C$ is étale, in the sense of `Algebra.Etale`, i.e. formally étale and of finite presentation over $\widehat O$.
--
--   This is the completed-base half of the étale-by-count criterion for a module-finite local extension of local domains: after base change to the completion of $O$, the hypotheses that the generic degree equals the residue degree and that the residue extension is separable force étaleness. It is used to derive the corresponding statement [`IsLocalRing.etale_of_finite_of_finrank_eq_finrank_residueField`](thm.html#IsLocalRing.etale_of_finite_of_finrank_eq_finrank_residueField) over the uncompleted base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_etale_adicCompletion_tensorProduct_of_finite_of_finrank_eq_finrank_residueField.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct in

theorem IsLocalRing.etale_adicCompletion_tensorProduct_of_finite_of_finrank_eq_finrank_residueField
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
    Algebra.Etale (AdicCompletion (IsLocalRing.maximalIdeal O) O)
      ((AdicCompletion (IsLocalRing.maximalIdeal O) O) ⊗[O] C) := by sorry
