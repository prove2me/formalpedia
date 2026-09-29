-- Prove2me | Theorems.Thm_HopfOrder_map_hopfKer_eq_inf_hopfKer
-- name    : HopfOrder.map_hopfKer_eq_inf_hopfKer
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/2bcf0a63-96ea-5dde-a640-a41ed3f1f937
-- title:
--   Integral Hopf kernel is the trace of the generic one
-- statement:
--   Let $R$ be a principal ideal domain with fraction field $K$, and let $A$ and $\bar A$ be commutative rings carrying Hopf algebra structures over $K$ together with $R$-algebra structures compatible with the tower $R \subseteq K$. Let $S$ be an $R$-subalgebra of $A$. Let $H$ be a commutative ring which is a Hopf algebra over $R$ and free as an $R$-module, and let $e : H \to A$ be an injective $R$-algebra map whose range is exactly $S$, compatible with comultiplication in the sense that for every $h \in H$ the $K$-comultiplication $\Delta_K(e(h))$ agrees with the image of $\Delta_R(h)$ under the $R$-algebra map $H \otimes_R H \to A \otimes_K A$ determined by $e$ followed by the left and right inclusions. Let $\pi : A \to \bar A$ be a $K$-bialgebra map, let $\bar H$ be a commutative ring which is a Hopf algebra over $R$ and free as an $R$-module, let $q : H \to \bar H$ be an $R$-bialgebra map, and let $\bar e : \bar H \to \bar A$ be an injective $R$-algebra map with $\bar e(q(h)) = \pi(e(h))$ for all $h$. The conclusion is an equality of $R$-subalgebras of $A$: the image under $e$ of $\{h \in H : (\mathrm{id} \otimes q)(\Delta_R h) = h \otimes 1\}$ equals the intersection of $S$ with $\{a \in A : (\mathrm{id} \otimes \pi)(\Delta_K a) = a \otimes 1\}$ viewed as an $R$-subalgebra, where in each case the displayed equaliser is the project's [`HopfAlgebra.hopfKer`](def/HopfAlgebra_HopfKer.html#L19) of the corresponding bialgebra map.
--
--   The statement compares the Hopf kernel of a map of Hopf orders over $R$ with the Hopf kernel of the corresponding map of generic fibres, identifying the former with the schematic closure of the latter inside the order; this is the step that converts an abstract torsor theorem for a surjection of finite free commutative Hopf algebras over $R$ into Raynaud's description of a prolongation as a torsor under the prolongation of the closed subgroup. It is used by [`HopfOrder.eq_of_le_of_comap_hopfKer_eq_of_map_eq`](thm.html#HopfOrder.eq_of_le_of_comap_hopfKer_eq_of_map_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfOrder_map_hopfKer_eq_inf_hopfKer.lean

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

theorem HopfOrder.map_hopfKer_eq_inf_hopfKer
    {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Type*} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
    {Ā : Type*} [CommRing Ā] [HopfAlgebra K Ā] [Algebra R Ā] [IsScalarTower R K Ā]
    (S : Subalgebra R A)
    {H : Type*} [CommRing H] [HopfAlgebra R H] [Module.Free R H]
    (e : H →ₐ[R] A) (he : Function.Injective e) (heS : e.range = S)
    (he_comul : ∀ h : H, Coalgebra.comul (R := K) (e h) =
        Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp e)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp e)
          (Coalgebra.comul (R := R) h))
    (π : A →ₐc[K] Ā)
    {Hbar : Type*} [CommRing Hbar] [HopfAlgebra R Hbar] [Module.Free R Hbar]
    (q : H →ₐc[R] Hbar) (ebar : Hbar →ₐ[R] Ā) (hebar : Function.Injective ebar)
    (hsq : ∀ h : H, ebar (q h) = π (e h)) :
    (HopfAlgebra.hopfKer q).map e = S ⊓ (HopfAlgebra.hopfKer π).restrictScalars R := by sorry
