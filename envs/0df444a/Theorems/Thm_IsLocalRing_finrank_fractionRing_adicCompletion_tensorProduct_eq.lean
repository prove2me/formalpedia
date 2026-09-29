-- Prove2me | Theorems.Thm_IsLocalRing_finrank_fractionRing_adicCompletion_tensorProduct_eq
-- name    : IsLocalRing.finrank_fractionRing_adicCompletion_tensorProduct_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/c4356bf2-2fc8-5aa8-85c3-ea21509a1a53
-- title:
--   Generic degree is unchanged by base change to the completion
-- statement:
--   Let $O$ be a Noetherian local domain and $C$ a domain which is an $O$-algebra, module-finite over $O$ and with faithful $O$-action (`FaithfulSMul O C`). Let $K_1$ and $K$ be fields that are fraction fields of $O$ and of $C$ respectively, equipped with algebra maps $K_1 \to K$ and $O \to K$ making the towers $O \subseteq C \subseteq K$ and $O \subseteq K_1 \subseteq K$ compatible. Write $\widehat O =$ `AdicCompletion (maximalIdeal O) O` for the completion of $O$ along its maximal ideal, and assume that both $\widehat O$ and $\widehat O \otimes_O C$ are domains. Let $L$ and $M$ be fields that are fraction fields of $\widehat O$ and of $\widehat O \otimes_O C$ respectively, with algebra maps $L \to M$ and $\widehat O \to M$ making the towers $\widehat O \subseteq \widehat O \otimes_O C \subseteq M$ and $\widehat O \subseteq L \subseteq M$ compatible. Then the $L$-dimension of $M$ equals the $K_1$-dimension of $K$: $[M:L] = [K:K_1]$.
--
--   The statement records that the generic degree of a module-finite extension of domains $O \subseteq C$ is preserved when one passes to the completion of the local base, in the form appropriate to arbitrary chosen fraction fields. It is used in the proof of [`IsLocalRing.etale_adicCompletion_tensorProduct_of_finite_of_finrank_eq_finrank_residueField`](thm.html#IsLocalRing.etale_adicCompletion_tensorProduct_of_finite_of_finrank_eq_finrank_residueField), the completed half of a criterion recognising étaleness of a finite algebra over a local ring by a comparison of ranks.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_finrank_fractionRing_adicCompletion_tensorProduct_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open IsLocalRing in
open scoped TensorProduct in

theorem IsLocalRing.finrank_fractionRing_adicCompletion_tensorProduct_eq
    {O : Type u} {C : Type v} [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsLocalRing O]
    [CommRing C] [IsDomain C] [Algebra O C] [Module.Finite O C] [FaithfulSMul O C]
    (K₁ K : Type*) [Field K₁] [Field K] [Algebra O K₁] [IsFractionRing O K₁]
    [Algebra C K] [IsFractionRing C K] [Algebra K₁ K] [Algebra O K]
    [IsScalarTower O C K] [IsScalarTower O K₁ K]
    [IsDomain (AdicCompletion (maximalIdeal O) O)] [IsDomain ((AdicCompletion (maximalIdeal O) O) ⊗[O] C)]
    (L M : Type*) [Field L] [Field M]
    [Algebra (AdicCompletion (maximalIdeal O) O) L] [IsFractionRing (AdicCompletion (maximalIdeal O) O) L]
    [Algebra ((AdicCompletion (maximalIdeal O) O) ⊗[O] C) M] [IsFractionRing ((AdicCompletion (maximalIdeal O) O) ⊗[O] C) M]
    [Algebra L M] [Algebra (AdicCompletion (maximalIdeal O) O) M]
    [IsScalarTower (AdicCompletion (maximalIdeal O) O) ((AdicCompletion (maximalIdeal O) O) ⊗[O] C) M]
    [IsScalarTower (AdicCompletion (maximalIdeal O) O) L M] :
    Module.finrank L M = Module.finrank K₁ K := by sorry
