-- Prove2me | Theorems.Thm_GaloisRep_exists_algEquiv_pi_of_finiteFlatHopf_of_galoisTrivial
-- name    : GaloisRep.exists_algEquiv_pi_of_finiteFlatHopf_of_galoisTrivial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/fe26a1ee-f19f-57b4-8087-866cb0ee1a21
-- title:
--   Galois-trivial finite flat Hopf algebras over ℤ_{(q)} are constant
-- statement:
--   Let $q$ be a prime with $q \neq 2$ and write $\mathbb{Z}_{(q)}$ for the subring of $\mathbb{Q}$ consisting of the rationals whose denominator is coprime to $q$ (the Lean [`GaloisRep.ratLocalizedAt q`](def/GaloisRep_Flat.html#L8)). Let $H$ be a commutative ring carrying a Hopf algebra structure over $\mathbb{Z}_{(q)}$ which is module-finite and flat over $\mathbb{Z}_{(q)}$ and whose comultiplication is cocommutative. Let $M$ be a finite additive abelian group equipped with a distributive multiplicative action of the group of $\mathbb{Q}$-algebra automorphisms of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, and let $e$ be a bijection from the set of $\mathbb{Z}_{(q)}$-algebra homomorphisms $H \to \overline{\mathbb{Q}}$, regarded as a monoid under convolution (`WithConv`), onto $M$, such that $e(f \ast g) = e(f) + e(g)$ and such that whenever $g = \sigma \circ f$ pointwise on $H$ one has $e(g) = \sigma \cdot e(f)$. Assume the Galois action on $M$ is trivial, that $q^{k} \cdot m = 0$ for all $m \in M$ for some $k$, and that $\#M = \operatorname{rank}_{\mathbb{Z}_{(q)}} H$. The conclusion has two parts: first, every such $f$ takes all its values in the image of $\mathbb{Z}_{(q)} \to \overline{\mathbb{Q}}$; second, there is an isomorphism $\varphi$ of $\mathbb{Z}_{(q)}$-algebras from $H$ to the algebra of $\mathbb{Z}_{(q)}$-valued functions on the set of these points, with $\varphi(x)(f)$ mapping to $f(x)$ in $\overline{\mathbb{Q}}$ for all $x \in H$ and all $f$.
--
--   This is the étale case of the Oort–Tate/Raynaud description of finite flat group schemes of $q$-power order over $\mathbb{Z}_{(q)}$ in the odd-residue-characteristic situation: under the stated hypotheses $\operatorname{Spec} H$ is the constant group scheme on its $\overline{\mathbb{Q}}$-points. It is used in the identification of Hopf algebras with group algebras in the cyclotomic case, [`GaloisRep.exists_bialgEquiv_monoidAlgebra_of_finiteFlatHopf_of_galoisCyclotomic`](thm.html#GaloisRep.exists_bialgEquiv_monoidAlgebra_of_finiteFlatHopf_of_galoisCyclotomic), and rests on the discrete valuation ring statement [`HopfAlgebra.exists_algEquiv_pi_of_injective_points_of_finrank_eq`](thm.html#HopfAlgebra.exists_algEquiv_pi_of_injective_points_of_finrank_eq) together with the integrality of Galois-trivial points [`GaloisRep.apply_mem_range_algebraMap_of_galoisTrivial`](thm.html#GaloisRep.apply_mem_range_algebraMap_of_galoisTrivial).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_exists_algEquiv_pi_of_finiteFlatHopf_of_galoisTrivial.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem GaloisRep.exists_algEquiv_pi_of_finiteFlatHopf_of_galoisTrivial
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt q) H]
    [Module.Finite (GaloisRep.ratLocalizedAt q) H] [Module.Flat (GaloisRep.ratLocalizedAt q) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt q) H]
    {M : Type} [AddCommGroup M] [Finite M]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) M]
    (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ) ≃ M)
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ)),
      (∀ x : H, g x = σ (f x)) → e g = σ • (e f))
    (htriv : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (m : M), σ • m = m)
    (htors : ∃ k : ℕ, ∀ m : M, q ^ k • m = 0)
    (hcard : Nat.card M = Module.finrank (GaloisRep.ratLocalizedAt q) H) :
    (∀ (f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ)) (x : H),
        (f x) ∈ (algebraMap (GaloisRep.ratLocalizedAt q) (AlgebraicClosure ℚ)).range) ∧
    ∃ φ : H ≃ₐ[GaloisRep.ratLocalizedAt q]
        (WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ) → GaloisRep.ratLocalizedAt q),
      ∀ (x : H) (f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ)),
        algebraMap (GaloisRep.ratLocalizedAt q) (AlgebraicClosure ℚ) (φ x f) = f x := by sorry
