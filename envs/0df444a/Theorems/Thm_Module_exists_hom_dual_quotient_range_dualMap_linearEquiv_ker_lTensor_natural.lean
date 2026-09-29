-- Prove2me | Theorems.Thm_Module_exists_hom_dual_quotient_range_dualMap_linearEquiv_ker_lTensor_natural
-- name    : Module.exists_hom_dual_quotient_range_dualMap_linearEquiv_ker_lTensor_natural
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/a48a4af5-0db2-52e1-a9e6-a347bb0a50bc
-- title:
--   Cokernel of the transpose corepresents ker(B ⊗ d)
-- statement:
--   Let $R$ be a commutative ring and let $d : K_0 \to K_1$ be an $R$-linear map between $R$-modules $K_0, K_1$ that are finite and free over $R$ (all three types lying in one universe). Write $d^\vee : K_1^\vee \to K_0^\vee$ for the dual map on $R$-linear duals and $E := K_0^\vee / \operatorname{im}(d^\vee)$ for the quotient of $K_0^\vee$ by the range of $d^\vee$. The assertion is that there exists a family $e$ assigning to every $R$-module $B$ in that universe an $R$-linear isomorphism $e_B : \operatorname{Hom}_R(E, B) \xrightarrow{\sim} \ker\bigl(\mathrm{id}_B \otimes d : B \otimes_R K_0 \to B \otimes_R K_1\bigr)$, subject to two conditions. First, naturality: for all $R$-modules $B, B'$, every $R$-linear $u : B \to B'$ and every $g : E \to B$, the element of $B' \otimes_R K_0$ underlying $e_{B'}(u \circ g)$ equals $(u \otimes \mathrm{id}_{K_0})$ applied to the element of $B \otimes_R K_0$ underlying $e_B(g)$. Second, an explicit description of the inverse: for every $B$, every $t \in \ker(\mathrm{id}_B \otimes d)$ and every $\varphi \in K_0^\vee$, the homomorphism $e_B^{-1}(t) : E \to B$ sends the class of $\varphi$ to the image of $(\mathrm{id}_B \otimes \varphi)(t) \in B \otimes_R R$ under the canonical isomorphism $B \otimes_R R \cong B$.
--
--   This is the statement that the functor $B \mapsto \ker(\mathrm{id}_B \otimes d)$ on $R$-modules is corepresented by the cokernel $E = \operatorname{coker}(d^\vee)$ of the transpose of $d$, together with the explicit formula for the corepresenting isomorphism. It is used in [`Module.nonempty_dual_quotient_range_dualMap_linearEquiv_quotient_of_forall_surjective_iff`](thm.html#Module.nonempty_dual_quotient_range_dualMap_linearEquiv_quotient_of_forall_surjective_iff), where kernels of base-changed maps are compared with quotients of a fixed module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_exists_hom_dual_quotient_range_dualMap_linearEquiv_ker_lTensor_natural.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open TensorProduct

theorem Module.exists_hom_dual_quotient_range_dualMap_linearEquiv_ker_lTensor_natural
    (R : Type u) [CommRing R]
    (K₀ K₁ : Type u) [AddCommGroup K₀] [Module R K₀] [Module.Finite R K₀] [Module.Free R K₀]
    [AddCommGroup K₁] [Module R K₁] [Module.Finite R K₁] [Module.Free R K₁]
    (d : K₀ →ₗ[R] K₁) :
    ∃ e : ∀ (B : Type u) [AddCommGroup B] [Module R B],
        ((Module.Dual R K₀ ⧸ LinearMap.range d.dualMap) →ₗ[R] B) ≃ₗ[R] LinearMap.ker (d.lTensor B),
      (∀ (B B' : Type u) [AddCommGroup B] [Module R B] [AddCommGroup B'] [Module R B'] (u : B →ₗ[R] B')
          (g : (Module.Dual R K₀ ⧸ LinearMap.range d.dualMap) →ₗ[R] B),
          ((e B' (u ∘ₗ g) : LinearMap.ker (d.lTensor B')) : B' ⊗[R] K₀) =
            u.rTensor K₀ ((e B g : LinearMap.ker (d.lTensor B)) : B ⊗[R] K₀)) ∧
      (∀ (B : Type u) [AddCommGroup B] [Module R B] (t : LinearMap.ker (d.lTensor B)) (φ : Module.Dual R K₀),
          (e B).symm t (Submodule.Quotient.mk φ) = TensorProduct.rid R B (φ.lTensor B (t : B ⊗[R] K₀))) := by sorry
