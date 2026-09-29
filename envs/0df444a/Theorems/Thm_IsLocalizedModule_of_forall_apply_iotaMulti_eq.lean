-- Prove2me | Theorems.Thm_IsLocalizedModule_of_forall_apply_iotaMulti_eq
-- name    : IsLocalizedModule.of_forall_apply_iotaMulti_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/e883cb65-d1c8-544c-94d0-048e5ba765ed
-- title:
--   Exterior powers commute with localisation of modules
-- statement:
--   Let $R$ be a commutative ring, $S \subseteq R$ a submonoid and $A$ a commutative $R$-algebra which is a localisation of $R$ at $S$. Let $M$ be an $R$-module, and let $N$ be an additive commutative group carrying compatible $R$- and $A$-module structures (an $R$-$A$ scalar tower). Let $f \colon M \to N$ be an $R$-linear map exhibiting $N$ as the localisation of $M$ at $S$, i.e. `IsLocalizedModule S f` holds. Fix $n \in \mathbb{N}$ and an $R$-linear map $F \colon \bigwedge^n_R M \to \bigwedge^n_A N$ (the source being the $n$-th exterior power over $R$, the target the $n$-th exterior power of $N$ over $A$, viewed as an $R$-module through the tower), and assume that $F$ carries pure wedges to pure wedges along $f$: for every family $m \colon \mathrm{Fin}\,n \to M$, $F(m_0 \wedge \dots \wedge m_{n-1}) = f(m_0) \wedge \dots \wedge f(m_{n-1})$. The conclusion is that $F$ itself is a localisation map at $S$, i.e. `IsLocalizedModule S F` holds: $\bigwedge^n_A N$ is the localisation of $\bigwedge^n_R M$ at $S$ via $F$.
--
--   This is the standard compatibility of exterior powers with localisation, in the form of a recognition criterion: any $R$-linear map between the two exterior powers that is multiplicative on pure wedges is automatically the localisation map. It is used in the verification that the map from the topological space level to sections over an affine open is bijective, [`AlgebraicGeometry.Scheme.Hom.topToSections_bijective_of_isAffineOpen`](thm.html#AlgebraicGeometry.Scheme.Hom.topToSections_bijective_of_isAffineOpen).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalizedModule_of_forall_apply_iotaMulti_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem IsLocalizedModule.of_forall_apply_iotaMulti_eq
    {R : Type*} [CommRing R] (S : Submonoid R) (A : Type*) [CommRing A] [Algebra R A] [IsLocalization S A]
    {M : Type*} [AddCommGroup M] [Module R M]
    {N : Type*} [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
    (f : M →ₗ[R] N) [IsLocalizedModule S f] (n : ℕ)
    (F : ⋀[R]^n M →ₗ[R] ⋀[A]^n N)
    (hF : ∀ m : Fin n → M, F (exteriorPower.ιMulti R n m) = exteriorPower.ιMulti A n (fun i => f (m i))) :
    IsLocalizedModule S F := by sorry
