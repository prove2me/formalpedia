-- Prove2me | Theorems.Thm_HopfAlgebra_exists_finiteFlat_padicInt_withConv_equiv_subquotient
-- name    : HopfAlgebra.exists_finiteFlat_padicInt_withConv_equiv_subquotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/e63a3f03-51fa-548c-85d5-e1b41859b8b9
-- title:
--   Galois-stable subquotients of points of finite flat ℤₚ-Hopf algebras
-- statement:
--   Let $p$ be a prime and write $\Gamma = \operatorname{Aut}(\overline{\mathbb{Q}}_p/\mathbb{Q}_p)$ for the group of $\mathbb{Q}_p$-algebra automorphisms of `AlgebraicClosure ℚ_[p]`. Let $C$ be a commutative ring carrying a Hopf algebra structure over $\mathbb{Z}_p$ which is finite and flat as a $\mathbb{Z}_p$-module and whose comultiplication is cocommutative. Let $P$ be an additive commutative group equipped with a distributive action of $\Gamma$, and let $eC$ be a bijection from `WithConv (C →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])`, the set of $\mathbb{Z}_p$-algebra homomorphisms $C \to \overline{\mathbb{Q}}_p$ with its convolution multiplication, onto $P$, such that $eC(f \cdot g) = eC(f) + eC(g)$ for all $f,g$, and such that whenever $\sigma \in \Gamma$ and $g(x) = \sigma(f(x))$ for all $x \in C$ one has $eC(g) = \sigma \cdot eC(f)$. Let $P' \le P$ be an additive subgroup with $\sigma \cdot x \in P'$ for all $\sigma \in \Gamma$ and $x \in P'$, let $N$ be an additive commutative group with a distributive $\Gamma$-action, and let $\pi \colon P' \to N$ be a surjective additive map satisfying $\pi(\sigma \cdot x) = \sigma \cdot \pi(x)$ for $\sigma \in \Gamma$, $x \in P'$. Then there is a commutative ring $H$ with a $\mathbb{Z}_p$-Hopf algebra structure, finite and flat as a $\mathbb{Z}_p$-module and cocommutative, together with a bijection $e$ from `WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])` onto $N$ carrying convolution to addition, $e(f \cdot g) = e(f) + e(g)$, and satisfying $e(g) = \sigma \cdot e(f)$ whenever $g(x) = \sigma(f(x))$ for all $x \in H$.
--
--   This is the Hopf-algebra form of the statement that a $\Gamma$-stable subquotient of the Galois module of $\overline{\mathbb{Q}}_p$-points of a finite flat commutative group scheme over $\mathbb{Z}_p$ is again the module of points of such a group scheme: the subgroup $P'$ is realised by passing to the schematic closure, and the quotient $N$ by an equivariant quotient construction. It is invoked in the construction of finite flat models for modules built from unramified and Kummer-type pieces.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_finiteFlat_padicInt_withConv_equiv_subquotient.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem HopfAlgebra.exists_finiteFlat_padicInt_withConv_equiv_subquotient
    (p : ℕ) [Fact p.Prime]
    (C : Type) [CommRing C] [HopfAlgebra ℤ_[p] C] [Module.Finite ℤ_[p] C] [Module.Flat ℤ_[p] C]
    [Coalgebra.IsCocomm ℤ_[p] C]
    {P : Type} [AddCommGroup P] [DistribMulAction (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) P]
    (eC : WithConv (C →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) ≃ P)
    (heC_add : ∀ f g, eC (f * g) = eC f + eC g)
    (heC_act : ∀ (σ : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])) (f g : WithConv (C →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])),
      (∀ x : C, g x = σ (f x)) → eC g = σ • (eC f))
    (P' : AddSubgroup P) (hP' : ∀ (σ : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])) (x : P), x ∈ P' → σ • x ∈ P')
    {N : Type} [AddCommGroup N] [DistribMulAction (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) N]
    (π : ↥P' →+ N) (hπ : Function.Surjective π)
    (hπ_act : ∀ (σ : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])) (x : ↥P'), π ⟨σ • (x : P), hP' σ x x.2⟩ = σ • π x) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H),
      Module.Finite ℤ_[p] H ∧ Module.Flat ℤ_[p] H ∧ Coalgebra.IsCocomm ℤ_[p] H ∧
      ∃ e : WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) ≃ N,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]))
          (f g : WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])),
          (∀ x : H, g x = σ (f x)) → e g = σ • (e f) := by sorry
