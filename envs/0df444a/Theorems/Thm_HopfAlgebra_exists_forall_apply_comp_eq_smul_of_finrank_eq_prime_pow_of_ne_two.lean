-- Prove2me | Theorems.Thm_HopfAlgebra_exists_forall_apply_comp_eq_smul_of_finrank_eq_prime_pow_of_ne_two
-- name    : HopfAlgebra.exists_forall_apply_comp_eq_smul_of_finrank_eq_prime_pow_of_ne_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/e3ba0ca1-6c28-5d5d-ad1d-b5560fb19c70
-- title:
--   A k-action on a finite flat p-group over ℤₚ
-- statement:
--   Fix a prime $p$ with $p \neq 2$, a field $k$, and an additive commutative group $M$ carrying a $k$-module structure together with a distributive action of the group of $\mathbb{Q}_p$-algebra automorphisms of `PadicAlgCl p` (the local Galois group of the situation) which commutes with the $k$-scalars. Let $H$ be a commutative ring that is a Hopf algebra over $\mathbb{Z}_p$, finite and free as a $\mathbb{Z}_p$-module, with cocommutative comultiplication, and suppose $\operatorname{rank}_{\mathbb{Z}_p} H = p^{a}$ for some $a \in \mathbb{N}$. Let $e$ be a bijection from `WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)`, the set of $\mathbb{Z}_p$-algebra maps $H \to$ `PadicAlgCl p` with its convolution monoid structure, onto $M$, such that $e(f \star g) = e(f) + e(g)$ and such that for every automorphism $\sigma$ and all $f, g$ with $g(x) = \sigma(f(x))$ for all $x \in H$ one has $e(g) = \sigma \cdot e(f)$. Then there is a family $\theta : k \to (H \to_{\mathrm{bialg}} H)$ of $\mathbb{Z}_p$-bialgebra endomorphisms of $H$ such that $e(f \circ \theta(a)) = a \cdot e(f)$ for all $a \in k$ and all $f$; such that $\theta(a)$ is the only bialgebra endomorphism with that property for the given $a$; and satisfying $\theta(ab) = \theta(a) \circ \theta(b)$, $\theta(1) = \mathrm{id}_H$, $\theta(a+b) = \theta(a) \star \theta(b)$ for the convolution product on algebra endomorphisms, and $\theta(0) = 1$ for the convolution unit.
--
--   This is the assertion that a finite flat commutative group scheme of $p$-power order over $\mathbb{Z}_p$ ($p$ odd) whose geometric points form a $k$-vector space with $k$-linear Galois action is a $k$-vector space scheme: the $k$-action on points descends uniquely to a ring homomorphism from $k$ into the endomorphisms of the group scheme, in Raynaud's sense. It is used to transport the coefficient field $k$ onto the integral model, and is cited in the construction of Honda systems attached to a residual Galois representation with bounded endomorphism rank.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_forall_apply_comp_eq_smul_of_finrank_eq_prime_pow_of_ne_two.lean

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped PadicInt

theorem HopfAlgebra.exists_forall_apply_comp_eq_smul_of_finrank_eq_prime_pow_of_ne_two
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    {k : Type} [Field k] {M : Type} [AddCommGroup M] [Module k M]
    [DistribMulAction (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) M]
    [SMulCommClass (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) k M]
    (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H] [Module.Finite ℤ_[p] H] [Module.Free ℤ_[p] H]
    [Coalgebra.IsCocomm ℤ_[p] H] (hrank : ∃ a : ℕ, Module.finrank ℤ_[p] H = p ^ a)
    (e : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) ≃ M)
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_act : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
      (f g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)), (∀ x : H, g x = σ (f x)) → e g = σ • (e f)) :
    ∃ θ : k → (H →ₐc[ℤ_[p]] H),
      (∀ (a : k) (f : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)),
        e (WithConv.toConv ((WithConv.ofConv f).comp (θ a : H →ₐ[ℤ_[p]] H))) = a • e f) ∧
      (∀ (a : k) (g : H →ₐc[ℤ_[p]] H),
        (∀ f : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p),
          e (WithConv.toConv ((WithConv.ofConv f).comp (g : H →ₐ[ℤ_[p]] H))) = a • e f) → g = θ a) ∧
      (∀ a b : k, θ (a * b) = (θ a).comp (θ b)) ∧
      θ 1 = BialgHom.id ℤ_[p] H ∧
      (∀ a b : k, WithConv.toConv (θ (a + b) : H →ₐ[ℤ_[p]] H) =
        WithConv.toConv (θ a : H →ₐ[ℤ_[p]] H) * WithConv.toConv (θ b : H →ₐ[ℤ_[p]] H)) ∧
      WithConv.toConv (θ 0 : H →ₐ[ℤ_[p]] H) = 1 := by sorry
