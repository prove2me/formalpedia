-- Prove2me | Theorems.Thm_IsLocalRing_exists_isLocalRing_adicCompletion_tensorProduct_residueField_equiv
-- name    : IsLocalRing.exists_isLocalRing_adicCompletion_tensorProduct_residueField_equiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/35883e75-dad0-5803-8c4e-9f4572cb3816
-- title:
--   widehat O⊗_O C is complete local with residue field κ(C)
-- statement:
--   Let $O$ and $C$ be Noetherian local commutative rings, with $C$ an $O$-algebra that is module-finite over $O$ and such that $\mathrm{algebraMap}\,O\,C$ is a local homomorphism. Write $\widehat O =$ `AdicCompletion (maximalIdeal O) O` and $T = \widehat O \otimes_O C$. The assertion is that there exist a local ring structure on $T$, a proof that the structure map $\widehat O \to T$ is a local homomorphism, and a ring isomorphism $e \colon \kappa(C) \to \kappa(T)$ between the residue fields, such that: $T$ is complete for the adic filtration by its maximal ideal; if the $\mathfrak m_C$-adic completion `AdicCompletion (maximalIdeal C) C` is a domain then so is $T$; if the $O$-action on $C$ is faithful then the $\widehat O$-action on $T$ is faithful; and $e$ is compatible with the map $c \mapsto 1 \otimes c$, i.e. $e(\mathrm{residue}_C(c)) = \mathrm{residue}_T(1 \otimes_O c)$ for every $c \in C$. Note that the local ring and local-homomorphism data are existentially quantified rather than produced as instances.
--
--   This is the completed-fibre package for a module-finite local extension: the base change of $C$ along $O \to \widehat O$ is again a complete local ring, with the same residue field as $C$ (underlying it is the identification of $\widehat O \otimes_O C$ with the $\mathfrak m_C$-adic completion of $C$). It is used in the verification of étaleness of such a base change from an equality of residue-field degrees.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_exists_isLocalRing_adicCompletion_tensorProduct_residueField_equiv.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open IsLocalRing in
open scoped TensorProduct in

theorem IsLocalRing.exists_isLocalRing_adicCompletion_tensorProduct_residueField_equiv
    {O : Type u} {C : Type v} [CommRing O] [IsNoetherianRing O] [IsLocalRing O]
    [CommRing C] [IsNoetherianRing C] [IsLocalRing C]
    [Algebra O C] [Module.Finite O C] [IsLocalHom (algebraMap O C)] :
    ∃ (_ : IsLocalRing ((AdicCompletion (maximalIdeal O) O) ⊗[O] C))
      (_ : IsLocalHom (algebraMap (AdicCompletion (maximalIdeal O) O) ((AdicCompletion (maximalIdeal O) O) ⊗[O] C)))
      (e : ResidueField C ≃+* ResidueField ((AdicCompletion (maximalIdeal O) O) ⊗[O] C)),
      IsAdicComplete (maximalIdeal ((AdicCompletion (maximalIdeal O) O) ⊗[O] C))
        ((AdicCompletion (maximalIdeal O) O) ⊗[O] C) ∧
      (IsDomain (AdicCompletion (maximalIdeal C) C) → IsDomain ((AdicCompletion (maximalIdeal O) O) ⊗[O] C)) ∧
      (FaithfulSMul O C → FaithfulSMul (AdicCompletion (maximalIdeal O) O) ((AdicCompletion (maximalIdeal O) O) ⊗[O] C)) ∧
      ∀ c : C, e (residue C c) = residue ((AdicCompletion (maximalIdeal O) O) ⊗[O] C) (1 ⊗ₜ[O] c) := by sorry
