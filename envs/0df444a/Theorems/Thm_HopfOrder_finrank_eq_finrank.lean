-- Prove2me | Theorems.Thm_HopfOrder_finrank_eq_finrank
-- name    : HopfOrder.finrank_eq_finrank
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/a650fa95-1e48-5be1-932e-e208c4f082d2
-- title:
--   Rank of an R-order equals the K-dimension it spans
-- statement:
--   Let $R$ be a commutative ring which is a domain and a principal ideal ring, let $K$ be a field that is an $R$-algebra and a fraction field of $R$ (in the sense of the `IsFractionRing` class), and let $A$ be a commutative ring carrying a Hopf algebra structure over $K$ together with an $R$-algebra structure compatible with that of $K$ via the scalar tower $R \to K \to A$. Let $S$ be an $R$-subalgebra of $A$ which is finite as an $R$-module, and assume that the $K$-span of the underlying set of $S$ inside $A$ is all of $A$. Then the $R$-rank of $S$ equals the $K$-dimension of $A$, both taken as `Module.finrank`. No hypothesis of flatness, separability or finite dimensionality of $A$ over $K$ is imposed beyond what follows from the two conditions on $S$.
--
--   This is the basic rank computation for an order $S$ in a $K$-algebra $A$: a finite $R$-submodule-algebra spanning $A$ over $K$ has $R$-rank equal to $\dim_K A$. It is used in the treatment of finite flat group schemes and their Hopf orders, in particular by [`HopfAlgebra.FVect.hopfOrder_eq_of_le_of_forall_act_mem`](thm.html#HopfAlgebra.FVect.hopfOrder_eq_of_le_of_forall_act_mem), by [`HopfAlgebra.exists_model_points_genericFibre_of_finite_flat_of_inertiaStable_step`](thm.html#HopfAlgebra.exists_model_points_genericFibre_of_finite_flat_of_inertiaStable_step) and by [`HopfOrder.finrank_eq_finrank_comap_hopfKer_mul_finrank_map`](thm.html#HopfOrder.finrank_eq_finrank_comap_hopfKer_mul_finrank_map).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfOrder_finrank_eq_finrank.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

theorem HopfOrder.finrank_eq_finrank
    {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Type*} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
    (S : Subalgebra R A)
    (hfin : Module.Finite R ↥S) (hspan : Submodule.span K (S : Set A) = ⊤) :
    Module.finrank R ↥S = Module.finrank K A := by sorry
