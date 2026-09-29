-- Prove2me | Theorems.Thm_HopfAlgebra_exists_bialgHom_surjective_range_eq_hopfKer_of_exact_of_ne_two
-- name    : HopfAlgebra.exists_bialgHom_surjective_range_eq_hopfKer_of_exact_of_ne_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/694f2808-9e93-5147-88e9-b0c96d064695
-- title:
--   Finite flat models of a short exact Galois sequence, p odd
-- statement:
--   Let $p$ be a prime with $p \neq 2$, and write $G = \mathrm{PadicAlgCl}\,p \simeq_{\mathbb{Q}_p} \mathrm{PadicAlgCl}\,p$ for the group of $\mathbb{Q}_p$-algebra automorphisms of `PadicAlgCl p`. Let $M_1, M_2, M_3$ be additive commutative groups each carrying a distributive $G$-action, and let $\alpha : M_1 \to M_2$, $\beta : M_2 \to M_3$ be additive maps which are $G$-equivariant, with $\alpha$ injective, $\beta$ surjective and the pair $(\alpha,\beta)$ exact (the kernel of $\beta$ is the image of $\alpha$). For $i = 1,2,3$ let $H_i$ be a commutative ring which is a Hopf algebra over $\mathbb{Z}_p$, finite and free as a $\mathbb{Z}_p$-module with cocommutative comultiplication and with $\mathrm{finrank}_{\mathbb{Z}_p} H_i = p^{a_i}$ for some natural number $a_i$, and let $e_i$ be a bijection from `WithConv (H i →ₐ[ℤ_[p]] PadicAlgCl p)`, the set of $\mathbb{Z}_p$-algebra homomorphisms $H_i \to \mathrm{PadicAlgCl}\,p$ with its convolution monoid structure, onto $M_i$, such that $e_i$ carries the convolution product to addition, $e_i(f*g) = e_i f + e_i g$, and is equivariant in the sense that whenever $g = \sigma \circ f$ pointwise on $H_i$ for $\sigma \in G$ one has $e_i g = \sigma \cdot e_i f$. Then there exist bialgebra homomorphisms $\pi : H_2 \to H_1$ and $j : H_3 \to H_2$ over $\mathbb{Z}_p$ such that: precomposition with $\pi$ induces $\alpha$ on points, i.e. $e_2(f \circ \pi) = \alpha(e_1 f)$ for every $f : H_1 \to \mathrm{PadicAlgCl}\,p$; precomposition with $j$ induces $\beta$, i.e. $e_3(f \circ j) = \beta(e_2 f)$ for every $f : H_2 \to \mathrm{PadicAlgCl}\,p$; $\pi$ is surjective; $j$ is injective; and the image of $j$ as an algebra homomorphism equals [`HopfAlgebra.hopfKer π`](def/HopfAlgebra_HopfKer.html#L19), the subalgebra of $H_2$ on which the coaction $(\mathrm{id}_{H_2} \otimes \pi) \circ \Delta_{H_2} : H_2 \to H_2 \otimes_{\mathbb{Z}_p} H_1$ agrees with $a \mapsto a \otimes 1$.
--
--   This is the statement that finite flat $\mathbb{Z}_p$-models of a short exact sequence of $\mathrm{Gal}(\overline{\mathbb{Q}}_p/\mathbb{Q}_p)$-modules of $p$-power order assemble, for odd $p$, into a short exact sequence of finite flat group schemes: a closed immersion $\operatorname{Spec} H_3 \hookrightarrow \operatorname{Spec} H_2$ identified with the kernel of the faithfully flat quotient map onto $\operatorname{Spec} H_1$, phrased on the Hopf-algebra side with the Hopf kernel in place of the scheme-theoretic kernel. It is used in the construction of Fontaine–Conrad style presentations of locally flat cocycles for residual Galois representations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_bialgHom_surjective_range_eq_hopfKer_of_exact_of_ne_two.lean

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_HopfAlgebra_HopfKer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped PadicInt

theorem HopfAlgebra.exists_bialgHom_surjective_range_eq_hopfKer_of_exact_of_ne_two
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    {M₁ M₂ M₃ : Type} [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
    [DistribMulAction (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) M₁]
    [DistribMulAction (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) M₂]
    [DistribMulAction (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) M₃]
    (α : M₁ →+ M₂) (β : M₂ →+ M₃)
    (hα : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (m : M₁), α (σ • m) = σ • α m)
    (hβ : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (m : M₂), β (σ • m) = σ • β m)
    (hαi : Function.Injective α) (hβs : Function.Surjective β) (hex : Function.Exact α β)
    (H₁ : Type) [CommRing H₁] [HopfAlgebra ℤ_[p] H₁] [Module.Finite ℤ_[p] H₁] [Module.Free ℤ_[p] H₁]
    [Coalgebra.IsCocomm ℤ_[p] H₁] (hrank₁ : ∃ a : ℕ, Module.finrank ℤ_[p] H₁ = p ^ a)
    (e₁ : WithConv (H₁ →ₐ[ℤ_[p]] PadicAlgCl p) ≃ M₁)
    (he₁_add : ∀ f g, e₁ (f * g) = e₁ f + e₁ g)
    (he₁_act : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
      (f g : WithConv (H₁ →ₐ[ℤ_[p]] PadicAlgCl p)), (∀ x : H₁, g x = σ (f x)) → e₁ g = σ • e₁ f)
    (H₂ : Type) [CommRing H₂] [HopfAlgebra ℤ_[p] H₂] [Module.Finite ℤ_[p] H₂] [Module.Free ℤ_[p] H₂]
    [Coalgebra.IsCocomm ℤ_[p] H₂] (hrank₂ : ∃ a : ℕ, Module.finrank ℤ_[p] H₂ = p ^ a)
    (e₂ : WithConv (H₂ →ₐ[ℤ_[p]] PadicAlgCl p) ≃ M₂)
    (he₂_add : ∀ f g, e₂ (f * g) = e₂ f + e₂ g)
    (he₂_act : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
      (f g : WithConv (H₂ →ₐ[ℤ_[p]] PadicAlgCl p)), (∀ x : H₂, g x = σ (f x)) → e₂ g = σ • e₂ f)
    (H₃ : Type) [CommRing H₃] [HopfAlgebra ℤ_[p] H₃] [Module.Finite ℤ_[p] H₃] [Module.Free ℤ_[p] H₃]
    [Coalgebra.IsCocomm ℤ_[p] H₃] (hrank₃ : ∃ a : ℕ, Module.finrank ℤ_[p] H₃ = p ^ a)
    (e₃ : WithConv (H₃ →ₐ[ℤ_[p]] PadicAlgCl p) ≃ M₃)
    (he₃_add : ∀ f g, e₃ (f * g) = e₃ f + e₃ g)
    (he₃_act : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
      (f g : WithConv (H₃ →ₐ[ℤ_[p]] PadicAlgCl p)), (∀ x : H₃, g x = σ (f x)) → e₃ g = σ • e₃ f) :
    ∃ (π : H₂ →ₐc[ℤ_[p]] H₁) (j : H₃ →ₐc[ℤ_[p]] H₂),
      (∀ f : WithConv (H₁ →ₐ[ℤ_[p]] PadicAlgCl p),
        e₂ (WithConv.toConv ((WithConv.ofConv f).comp (π : H₂ →ₐ[ℤ_[p]] H₁))) = α (e₁ f)) ∧
      (∀ f : WithConv (H₂ →ₐ[ℤ_[p]] PadicAlgCl p),
        e₃ (WithConv.toConv ((WithConv.ofConv f).comp (j : H₃ →ₐ[ℤ_[p]] H₂))) = β (e₂ f)) ∧
      Function.Surjective π ∧ Function.Injective j ∧
      (j : H₃ →ₐ[ℤ_[p]] H₂).range = HopfAlgebra.hopfKer π := by sorry
