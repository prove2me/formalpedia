-- Prove2me | Theorems.Thm_GaloisRep_exists_finiteFlat_of_subalgebra_pi_algebraicClosure
-- name    : GaloisRep.exists_finiteFlat_of_subalgebra_pi_algebraicClosure
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/53413598-e1b2-5010-8823-89e5341d25ef
-- title:
--   Galois-equivariant Hopf orders give finite flat models
-- statement:
--   Let $p$ be a natural number assumed prime, and write $R = \mathbb{Z}_{(p)}$ for the subring [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ consisting of those rationals whose denominator is coprime to $p$. Let $X$ be a finite additive commutative group carrying a distributive action of the group $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ`, i.e. an action by additive automorphisms. Let $B$ be an $R$-subalgebra of the algebra of all functions $X \to \overline{\mathbb{Q}}$ with pointwise operations, subject to: $B$, viewed as an $R$-submodule, is finitely generated; every $F \in B$ satisfies $F(\sigma \cdot x) = \sigma(F(x))$ for all $\sigma$ and $x$; every $F \in B$ admits an addition law $F(x+y) = \sum_{i<n} F_{1,i}(x)\,F_{2,i}(y)$ for some $n$ and some $F_{1,i}, F_{2,i} \in B$; $B$ is stable under $F \mapsto F(-\,\cdot\,)$; and $B$ separates points of $X$, in the sense that $F(x) = F(y)$ for all $F \in B$ forces $x = y$. The conclusion asserts the existence of a type $H$ with a commutative ring structure and a Hopf algebra structure over $R$ such that $H$ is finite and flat as an $R$-module, its coalgebra structure is cocommutative, and there is a bijection $e$ from the set of $R$-algebra homomorphisms $H \to \overline{\mathbb{Q}}$, equipped with the convolution multiplication (`WithConv`), onto $X$, satisfying $e(f \ast g) = e(f) + e(g)$ and, whenever $g(x) = \sigma(f(x))$ for all $x \in H$, $e(g) = \sigma \cdot e(f)$.
--
--   This is the recognition principle that a Galois-equivariant Hopf order, inside the algebra of $\overline{\mathbb{Q}}$-valued functions on a finite Galois module $X$, is the coordinate ring of a finite flat commutative group scheme over $\mathbb{Z}_{(p)}$ whose $\overline{\mathbb{Q}}$-points recover $X$ with its Galois action. It supplies finite flat models in the form used for local conditions on Galois representations, and is invoked by [`GaloisRep.exists_finiteFlat_pi_of_forall_smul_eq_of_not_dvd_discr`](thm.html#GaloisRep.exists_finiteFlat_pi_of_forall_smul_eq_of_not_dvd_discr) and by [`GaloisRepAdic.isFlatAt_ofResidualGaloisRep_of_isUnramifiedAt`](thm.html#GaloisRepAdic.isFlatAt_ofResidualGaloisRep_of_isUnramifiedAt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_exists_finiteFlat_of_subalgebra_pi_algebraicClosure.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem GaloisRep.exists_finiteFlat_of_subalgebra_pi_algebraicClosure (p : ℕ) (hp : p.Prime)
    {X : Type} [AddCommGroup X] [Finite X]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) X]
    (B : Subalgebra (GaloisRep.ratLocalizedAt p) (X → AlgebraicClosure ℚ))
    (hfin : (Subalgebra.toSubmodule B).FG)
    (hequiv : ∀ F ∈ B, ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : X),
      F (σ • x) = σ (F x))
    (hcomul : ∀ F ∈ B, ∃ (n : ℕ) (F₁ F₂ : Fin n → X → AlgebraicClosure ℚ),
      (∀ i, F₁ i ∈ B) ∧ (∀ i, F₂ i ∈ B) ∧ ∀ x y : X, F (x + y) = ∑ i, F₁ i x * F₂ i y)
    (hneg : ∀ F ∈ B, (fun x => F (-x)) ∈ B)
    (hsep : ∀ x y : X, (∀ F ∈ B, F x = F y) → x = y) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) H),
      Module.Finite (GaloisRep.ratLocalizedAt p) H ∧ Module.Flat (GaloisRep.ratLocalizedAt p) H ∧
      Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H ∧
      ∃ e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ X,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
          (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
          (∀ x : H, g x = σ (f x)) → e g = σ • (e f) := by sorry
