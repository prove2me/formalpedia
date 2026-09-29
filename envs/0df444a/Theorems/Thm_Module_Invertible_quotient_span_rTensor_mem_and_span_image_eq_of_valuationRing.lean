-- Prove2me | Theorems.Thm_Module_Invertible_quotient_span_rTensor_mem_and_span_image_eq_of_valuationRing
-- name    : Module.Invertible.quotient_span_rTensor_mem_and_span_image_eq_of_valuationRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/3178178b-697c-5b77-9e19-02ef2faa92e0
-- title:
--   Saturation over a valuation ring of a co-invertible subspace
-- statement:
--   Let $\mathcal O$ be a commutative ring, let $V$ be an $\mathcal O$-algebra which is a valuation ring and an integral domain, and let $L$ be a field which is an $\mathcal O$-algebra and a $V$-algebra, compatibly ($L$ is an $\mathcal O$-algebra via $V$), and which is a fraction field of $V$. Let $M$ be a finitely generated $\mathcal O$-module. Write $\iota$ for the map $V \otimes_{\mathcal O} M \to L \otimes_{\mathcal O} M$ obtained by tensoring the structure map $V \to L$ with $M$ (the `rTensor` of the underlying linear map of `IsScalarTower.toAlgHom 𝒪 V L`). Let $N$ be an $L$-submodule of $L \otimes_{\mathcal O} M$ such that the quotient $(L \otimes_{\mathcal O} M)/N$ is an invertible $L$-module. Set $N_0 := \operatorname{span}_V \{x \in V \otimes_{\mathcal O} M : \iota(x) \in N\}$, the $V$-span of the preimage of $N$ under $\iota$. The conclusion is twofold: first, the quotient $(V \otimes_{\mathcal O} M)/N_0$ is an invertible $V$-module; second, the $L$-span of the image $\iota(N_0) \subseteq L \otimes_{\mathcal O} M$ is exactly $N$.
--
--   This is the saturation construction for a hyperplane-type subspace over a valuation ring: an $L$-point of the projective space of $L \otimes_{\mathcal O} M$ extends to a $V$-point of the projective space of $V \otimes_{\mathcal O} M$, with the generic fibre recovered by base change to $L$. It is used in the Čerednik–Drinfel'd part of the development, in the valuative criteria [`CerednikDrinfeld.FormalOmega.DeligneDatum.exists_edge_nondeg_saturation_of_valuationRing`](thm.html#CerednikDrinfeld.FormalOmega.DeligneDatum.exists_edge_nondeg_saturation_of_valuationRing) and [`CerednikDrinfeld.FormalOmega.DeligneDatum.exists_isBaseChange_of_valuationRing_of_map_eq_zero`](thm.html#CerednikDrinfeld.FormalOmega.DeligneDatum.exists_isBaseChange_of_valuationRing_of_map_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_Invertible_quotient_span_rTensor_mem_and_span_image_eq_of_valuationRing.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w

open scoped TensorProduct

theorem Module.Invertible.quotient_span_rTensor_mem_and_span_image_eq_of_valuationRing
    {𝒪 : Type u} [CommRing 𝒪]
    (V : Type v) [CommRing V] [IsDomain V] [ValuationRing V] [Algebra 𝒪 V]
    (L : Type v) [Field L] [Algebra 𝒪 L] [Algebra V L] [IsScalarTower 𝒪 V L] [IsFractionRing V L]
    (M : Type w) [AddCommGroup M] [Module 𝒪 M] [Module.Finite 𝒪 M]
    (N : Submodule L (L ⊗[𝒪] M)) (hN : Module.Invertible L ((L ⊗[𝒪] M) ⧸ N)) :
    Module.Invertible V ((V ⊗[𝒪] M) ⧸ Submodule.span V
        {x : V ⊗[𝒪] M | LinearMap.rTensor M (IsScalarTower.toAlgHom 𝒪 V L).toLinearMap x ∈ N}) ∧
      Submodule.span L (LinearMap.rTensor M (IsScalarTower.toAlgHom 𝒪 V L).toLinearMap ''
        (Submodule.span V {x : V ⊗[𝒪] M | LinearMap.rTensor M (IsScalarTower.toAlgHom 𝒪 V L).toLinearMap x ∈ N} :
          Set (V ⊗[𝒪] M))) = N := by sorry
