-- Prove2me | Theorems.Thm_HopfAlgebra_existsUnique_bialgHom_forall_apply_comp_eq_of_finrank_eq_prime_pow_of_ne_two
-- name    : HopfAlgebra.existsUnique_bialgHom_forall_apply_comp_eq_of_finrank_eq_prime_pow_of_ne_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/f5518d0b-e820-5e3a-9ab0-1cb30ed29850
-- title:
--   Full faithfulness of the generic fibre over ℤₚ, p odd
-- statement:
--   Let $p$ be an odd prime, and write $\overline{\mathbb{Q}}_p$ for `PadicAlgCl p` and $G_p = \overline{\mathbb{Q}}_p \simeq_{\mathbb{Q}_p} \overline{\mathbb{Q}}_p$ for its group of $\mathbb{Q}_p$-algebra automorphisms. Let $M_1, M_2$ be additive commutative groups carrying distributive $G_p$-actions. Let $H_1$ be a commutative ring which is a cocommutative Hopf algebra over $\mathbb{Z}_p$, finite and free as a $\mathbb{Z}_p$-module, with $\operatorname{rank}_{\mathbb{Z}_p} H_1 = p^{a}$ for some $a \in \mathbb{N}$, and let $e_1$ be a bijection from `WithConv (H₁ →ₐ[ℤ_[p]] PadicAlgCl p)`, the set of $\mathbb{Z}_p$-algebra maps $H_1 \to \overline{\mathbb{Q}}_p$ with its convolution monoid structure, onto $M_1$, such that $e_1(f * g) = e_1 f + e_1 g$ for all $f, g$, and such that whenever $\sigma \in G_p$ and $g$ satisfies $g(x) = \sigma(f(x))$ for all $x \in H_1$ one has $e_1 g = \sigma \cdot e_1 f$. Let $H_2$, with $\operatorname{rank}_{\mathbb{Z}_p} H_2$ a power of $p$, and $e_2$ satisfy the same hypotheses. Let $\varphi : M_1 \to M_2$ be an additive map with $\varphi(\sigma \cdot m) = \sigma \cdot \varphi(m)$ for all $\sigma \in G_p$, $m \in M_1$. Then there is exactly one $\mathbb{Z}_p$-bialgebra homomorphism $g : H_2 \to H_1$ such that for every $f : H_1 \to \overline{\mathbb{Q}}_p$ the composite $g$ followed by $f$, viewed in the convolution monoid of $H_2$, satisfies $e_2(f \circ g) = \varphi(e_1 f)$.
--
--   In scheme language this is the full faithfulness of the generic-fibre functor on finite flat commutative group schemes of $p$-power order over $\mathbb{Z}_p$ (Raynaud's criterion in the case of absolute ramification index $1 < p-1$, whence the exclusion of $p = 2$): a Galois-equivariant homomorphism between the groups of $\overline{\mathbb{Q}}_p$-points comes from a unique homomorphism $\operatorname{Spec} H_1 \to \operatorname{Spec} H_2$ of group schemes over $\mathbb{Z}_p$. It is used in the project to transport maps of $p$-adic Galois modules back to maps of finite flat group schemes, and feeds the statements [`HopfAlgebra.exists_bialgHom_surjective_range_eq_hopfKer_of_exact_of_ne_two`](thm.html#HopfAlgebra.exists_bialgHom_surjective_range_eq_hopfKer_of_exact_of_ne_two), [`HopfAlgebra.exists_coeffAction_forall_apply_comp_eq_smul_of_ne_two`](thm.html#HopfAlgebra.exists_coeffAction_forall_apply_comp_eq_smul_of_ne_two) and [`HopfAlgebra.exists_forall_apply_comp_eq_smul_of_finrank_eq_prime_pow_of_ne_two`](thm.html#HopfAlgebra.exists_forall_apply_comp_eq_smul_of_finrank_eq_prime_pow_of_ne_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_existsUnique_bialgHom_forall_apply_comp_eq_of_finrank_eq_prime_pow_of_ne_two.lean

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped PadicInt

theorem HopfAlgebra.existsUnique_bialgHom_forall_apply_comp_eq_of_finrank_eq_prime_pow_of_ne_two
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    {M₁ M₂ : Type} [AddCommGroup M₁] [AddCommGroup M₂]
    [DistribMulAction (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) M₁]
    [DistribMulAction (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) M₂]
    (H₁ : Type) [CommRing H₁] [HopfAlgebra ℤ_[p] H₁] [Module.Finite ℤ_[p] H₁] [Module.Free ℤ_[p] H₁]
    [Coalgebra.IsCocomm ℤ_[p] H₁] (hrank₁ : ∃ a : ℕ, Module.finrank ℤ_[p] H₁ = p ^ a)
    (e₁ : WithConv (H₁ →ₐ[ℤ_[p]] PadicAlgCl p) ≃ M₁)
    (he₁_add : ∀ f g, e₁ (f * g) = e₁ f + e₁ g)
    (he₁_act : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
      (f g : WithConv (H₁ →ₐ[ℤ_[p]] PadicAlgCl p)), (∀ x : H₁, g x = σ (f x)) → e₁ g = σ • (e₁ f))
    (H₂ : Type) [CommRing H₂] [HopfAlgebra ℤ_[p] H₂] [Module.Finite ℤ_[p] H₂] [Module.Free ℤ_[p] H₂]
    [Coalgebra.IsCocomm ℤ_[p] H₂] (hrank₂ : ∃ a : ℕ, Module.finrank ℤ_[p] H₂ = p ^ a)
    (e₂ : WithConv (H₂ →ₐ[ℤ_[p]] PadicAlgCl p) ≃ M₂)
    (he₂_add : ∀ f g, e₂ (f * g) = e₂ f + e₂ g)
    (he₂_act : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
      (f g : WithConv (H₂ →ₐ[ℤ_[p]] PadicAlgCl p)), (∀ x : H₂, g x = σ (f x)) → e₂ g = σ • (e₂ f))
    (φ : M₁ →+ M₂)
    (hφ : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (m : M₁), φ (σ • m) = σ • φ m) :
    ∃! g : H₂ →ₐc[ℤ_[p]] H₁,
      ∀ f : WithConv (H₁ →ₐ[ℤ_[p]] PadicAlgCl p),
        e₂ (WithConv.toConv ((WithConv.ofConv f).comp (g : H₂ →ₐ[ℤ_[p]] H₁))) = φ (e₁ f) := by sorry
