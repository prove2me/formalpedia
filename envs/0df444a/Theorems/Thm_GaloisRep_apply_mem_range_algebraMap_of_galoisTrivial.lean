-- Prove2me | Theorems.Thm_GaloisRep_apply_mem_range_algebraMap_of_galoisTrivial
-- name    : GaloisRep.apply_mem_range_algebraMap_of_galoisTrivial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/62cc342a-0f72-5bab-82d9-b6efbad21e4f
-- title:
--   Galois-trivial points of a module-finite Hopf algebra are ℤ_{(q)}-valued
-- statement:
--   Fix a natural number $q$ assumed prime, and write $R = \mathbb{Z}_{(q)}$ for [`GaloisRep.ratLocalizedAt q`](def/GaloisRep_Flat.html#L8), the subring of $\mathbb{Q}$ consisting of those rationals whose denominator is coprime to $q$. Let $H$ be a commutative ring equipped with a Hopf algebra structure over $R$ which is finite as an $R$-module, and let $M$ be an additive commutative group carrying a distributive multiplicative action of the group $G = \mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ of $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ`. Suppose given a bijection $e$ from the type of $R$-algebra homomorphisms $H \to \overline{\mathbb{Q}}$ (taken in its convolution type-synonym copy `WithConv`, whose elements are still such homomorphisms) onto $M$, which is equivariant in the following sense: whenever $\sigma \in G$ and $f, g$ are two such homomorphisms with $g(x) = \sigma(f(x))$ for all $x \in H$, then $e(g) = \sigma \cdot e(f)$. Suppose further that the action of $G$ on $M$ is trivial, i.e. $\sigma \cdot m = m$ for all $\sigma$ and all $m \in M$. Then for every such homomorphism $f$ and every $x \in H$, the value $f(x)$ lies in the image of the structure map $R \to \overline{\mathbb{Q}}$.
--
--   This is the Galois-descent step showing that the $\overline{\mathbb{Q}}$-points of a module-finite Hopf algebra over $\mathbb{Z}_{(q)}$ take values in $\mathbb{Z}_{(q)}$ as soon as the Galois action on them is trivial. It feeds into [`GaloisRep.exists_algEquiv_pi_of_finiteFlatHopf_of_galoisTrivial`](thm.html#GaloisRep.exists_algEquiv_pi_of_finiteFlatHopf_of_galoisTrivial), where such a Hopf algebra with trivial Galois action on its points is split as a product of copies of the base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_apply_mem_range_algebraMap_of_galoisTrivial.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem GaloisRep.apply_mem_range_algebraMap_of_galoisTrivial
    (q : ℕ) [Fact q.Prime]
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt q) H]
    [Module.Finite (GaloisRep.ratLocalizedAt q) H]
    {M : Type} [AddCommGroup M]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) M]
    (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ) ≃ M)
    (he_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ)),
      (∀ x : H, g x = σ (f x)) → e g = σ • (e f))
    (htriv : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (m : M), σ • m = m)
    (f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ)) (x : H) :
    f x ∈ (algebraMap (GaloisRep.ratLocalizedAt q) (AlgebraicClosure ℚ)).range := by sorry
