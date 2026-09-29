-- Prove2me | Theorems.Thm_HopfAlgebra_exists_algEquiv_baseChange_padic_comul_of_withConv_equiv
-- name    : HopfAlgebra.exists_algEquiv_baseChange_padic_comul_of_withConv_equiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/af1fb3b3-3e99-5dd2-9485-6f800fdfdc12
-- title:
--   Matching ℚ̄ₚ-point groups give isomorphic base-changed Hopf algebras
-- statement:
--   Fix a prime $p$. Let $A$ be a commutative ring carrying a Hopf algebra structure over $\mathbb{Q}$ which is finite as a $\mathbb{Q}$-module and cocommutative as a $\mathbb{Q}$-coalgebra, and let $H_p$ be a commutative ring carrying a Hopf algebra structure over $\mathbb{Z}_p$ which is finite and flat as a $\mathbb{Z}_p$-module and cocommutative. Let $M$ be an additive commutative group with a distributive multiplicative action of $\mathrm{Gal}(\overline{\mathbb{Q}_p}/\mathbb{Q}_p)$, realised as the group of $\mathbb{Q}_p$-algebra automorphisms of `AlgebraicClosure ℚ_[p]`. Assume given a bijection $e_{H_p}$ from `WithConv (Hp →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])`, the set of $\mathbb{Z}_p$-algebra homomorphisms $H_p \to \overline{\mathbb{Q}_p}$ equipped with its convolution multiplication, onto $M$, which carries the multiplication to addition and is Galois-equivariant in the sense that whenever $g$ is the pointwise composite of $f$ with $\sigma$ one has $e_{H_p}(g) = \sigma \cdot e_{H_p}(f)$; assume a bijection $e_{A}$ from `WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ_[p])` onto the same $M$ with the same two properties. Then there exists a $\mathbb{Q}_p$-algebra isomorphism $\varphi : \mathbb{Q}_p \otimes_{\mathbb{Q}} A \to \mathbb{Q}_p \otimes_{\mathbb{Z}_p} H_p$ such that $\Delta(\varphi x) = (\varphi \otimes \varphi)(\Delta x)$ for every $x$, the comultiplications being those of the two $\mathbb{Q}_p$-coalgebra structures. Compatibility with counit and antipode is not asserted.
--
--   This is the Grothendieck–Galois reconstruction step for finite Hopf algebras in characteristic $0$: two finite Hopf algebras, one over $\mathbb{Q}$ and one over $\mathbb{Z}_p$, whose groups of $\overline{\mathbb{Q}_p}$-points are identified with the same Galois module become isomorphic as $\mathbb{Q}_p$-bialgebras after base change to $\mathbb{Q}_p$. It feeds the construction of a finite flat model over $\mathbb{Z}_p$ of the $\mathbb{Q}$-group scheme in [`HopfAlgebra.exists_finiteFlat_ratLocalizedAt_of_padicInt_of_withConv_equiv`](thm.html#HopfAlgebra.exists_finiteFlat_ratLocalizedAt_of_padicInt_of_withConv_equiv).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_algEquiv_baseChange_padic_comul_of_withConv_equiv.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped NNReal TensorProduct

theorem HopfAlgebra.exists_algEquiv_baseChange_padic_comul_of_withConv_equiv
    (p : ℕ) [Fact p.Prime]
    (A : Type) [CommRing A] [HopfAlgebra ℚ A]
    (hAfin : Module.Finite ℚ A) (hAcocomm : Coalgebra.IsCocomm ℚ A)
    (Hp : Type) [CommRing Hp] [HopfAlgebra ℤ_[p] Hp]
    (hfin : Module.Finite ℤ_[p] Hp) (hflat : Module.Flat ℤ_[p] Hp)
    (hcocomm : Coalgebra.IsCocomm ℤ_[p] Hp)
    {M : Type} [AddCommGroup M]
    [DistribMulAction (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) M]
    (eHp : WithConv (Hp →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) ≃ M)
    (heHp_add : ∀ f g, eHp (f * g) = eHp f + eHp g)
    (heHp_act : ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
      (f g : WithConv (Hp →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])),
      (∀ x : Hp, g x = σ (f x)) → eHp g = σ • (eHp f))
    (eAp : WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ_[p]) ≃ M)
    (heAp_add : ∀ f g, eAp (f * g) = eAp f + eAp g)
    (heAp_act : ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
      (f g : WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ_[p])),
      (∀ a : A, g a = σ (f a)) → eAp g = σ • (eAp f)) :
    ∃ φ : (ℚ_[p] ⊗[ℚ] A) ≃ₐ[ℚ_[p]] (ℚ_[p] ⊗[ℤ_[p]] Hp),
      ∀ x, Coalgebra.comul (R := ℚ_[p]) (φ x) =
        (TensorProduct.map φ.toLinearMap φ.toLinearMap) (Coalgebra.comul (R := ℚ_[p]) x) := by sorry
