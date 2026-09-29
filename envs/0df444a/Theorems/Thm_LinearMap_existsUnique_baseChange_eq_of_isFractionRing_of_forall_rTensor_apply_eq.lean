-- Prove2me | Theorems.Thm_LinearMap_existsUnique_baseChange_eq_of_isFractionRing_of_forall_rTensor_apply_eq
-- name    : LinearMap.existsUnique_baseChange_eq_of_isFractionRing_of_forall_rTensor_apply_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/ddd08021-715f-5242-86f8-f9454531c924
-- title:
--   Descent of linear maps along K ∩ ̂ O = O
-- statement:
--   Let $O$ be a commutative domain, $K$ a field that is a fraction field of $O$ via its $O$-algebra structure, $\hat O$ a commutative $O$-algebra, and $\hat K$ a commutative ring carrying compatible algebra structures over $O$, over $K$ and over $\hat O$, the compatibility being that $O \to K \to \hat K$ and $O \to \hat O \to \hat K$ are scalar towers. Assume the structure map $\hat O \to \hat K$ is injective, and assume the cap property: for every $x \in K$ and $y \in \hat O$ having the same image in $\hat K$, there is $z \in O$ with $x$ the image of $z$ in $K$. Let $M$ and $N$ be finite free $O$-modules, let $f_K \colon K \otimes_O M \to K \otimes_O N$ be $K$-linear, and let $f_{\hat O} \colon \hat O \otimes_O M \to \hat O \otimes_O N$ be $\hat O$-linear, and assume that for every $m \in M$ the elements $f_K(1 \otimes m)$ and $f_{\hat O}(1 \otimes m)$ have the same image in $\hat K \otimes_O N$ under the maps induced on the left factor by $K \to \hat K$ and by $\hat O \to \hat K$ respectively. Then there is exactly one $O$-linear map $f \colon M \to N$ whose base changes to $K$ and to $\hat O$ are $f_K$ and $f_{\hat O}$.
--
--   This is the descent step usually written $\operatorname{Hom}_O(M,N) = \operatorname{Hom}_K(M_K,N_K) \cap \operatorname{Hom}_{\hat O}(M_{\hat O},N_{\hat O})$, the typical instance being $O$ a domain with $\hat O$ a completion and $\hat K$ a ring containing both $K$ and $\hat O$. It is used to reduce statements about $O$-linear structures on finite free modules to their fraction-field and completed counterparts; here it supports the corresponding descent statement for bialgebra homomorphisms, [`BialgHom.existsUnique_baseChange_eq_of_isFractionRing_of_forall_rTensor_apply_eq`](thm.html#BialgHom.existsUnique_baseChange_eq_of_isFractionRing_of_forall_rTensor_apply_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LinearMap_existsUnique_baseChange_eq_of_isFractionRing_of_forall_rTensor_apply_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u

open scoped TensorProduct

theorem LinearMap.existsUnique_baseChange_eq_of_isFractionRing_of_forall_rTensor_apply_eq
    (O : Type u) [CommRing O] [IsDomain O] (K : Type u) [Field K] [Algebra O K] [IsFractionRing O K]
    (Oh : Type u) [CommRing Oh] [Algebra O Oh]
    (Kh : Type u) [CommRing Kh] [Algebra O Kh] [Algebra K Kh] [Algebra Oh Kh] [IsScalarTower O K Kh] [IsScalarTower O Oh Kh]
    (hinj : Function.Injective (algebraMap Oh Kh))
    (hcap : ∀ (x : K) (y : Oh), algebraMap K Kh x = algebraMap Oh Kh y → ∃ z : O, algebraMap O K z = x)
    (M : Type u) [AddCommGroup M] [Module O M] [Module.Free O M] [Module.Finite O M]
    (N : Type u) [AddCommGroup N] [Module O N] [Module.Free O N] [Module.Finite O N]
    (fK : K ⊗[O] M →ₗ[K] K ⊗[O] N) (fOh : Oh ⊗[O] M →ₗ[Oh] Oh ⊗[O] N)
    (hagree : ∀ m : M,
      ((IsScalarTower.toAlgHom O K Kh).toLinearMap.rTensor N) (fK ((1 : K) ⊗ₜ m)) =
        ((IsScalarTower.toAlgHom O Oh Kh).toLinearMap.rTensor N) (fOh ((1 : Oh) ⊗ₜ m))) :
    ∃! f : M →ₗ[O] N, f.baseChange K = fK ∧ f.baseChange Oh = fOh := by sorry
