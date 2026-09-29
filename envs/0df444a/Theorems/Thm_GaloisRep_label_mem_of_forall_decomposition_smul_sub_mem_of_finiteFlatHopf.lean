-- Prove2me | Theorems.Thm_GaloisRep_label_mem_of_forall_decomposition_smul_sub_mem_of_finiteFlatHopf
-- name    : GaloisRep.label_mem_of_forall_decomposition_smul_sub_mem_of_finiteFlatHopf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/383cb7cd-4658-535c-b8f6-a73c7fb7f4fc
-- title:
--   Labelling q-power points that reduce to the identity
-- statement:
--   Let $q$ be a prime with $q \neq 2$, and write $\mathbb{Z}_{(q)}$ for the subring [`GaloisRep.ratLocalizedAt q`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ consisting of those rationals whose denominator is coprime to $q$. Let $H$ be a commutative ring which is a cocommutative Hopf algebra over $\mathbb{Z}_{(q)}$, finite and flat as a $\mathbb{Z}_{(q)}$-module. Let $J$ be an additive abelian group carrying a distributive action of the group of $\mathbb{Q}$-algebra automorphisms of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, let $M \le J$ be an additive subgroup, and let $e$ be a bijection from `WithConv` of the set of $\mathbb{Z}_{(q)}$-algebra maps $H \to \overline{\mathbb{Q}}$ onto $M$ such that $e(fg) = e(f) + e(g)$, and such that whenever $\sigma$ is an automorphism and $g$ is the point with $g(h) = \sigma(f(h))$ for all $h \in H$, one has $e(g) = \sigma \cdot e(f)$ in $J$. Let $A_q$ be a valuation subring of $\overline{\mathbb{Q}}$ in which the image of $q$ is a non-unit, let $m$ be a natural number, and let $N \le J$ be an additive subgroup stable under the decomposition subgroup of $A_q$ over $\mathbb{Q}$. Let $x$ be a point satisfying: the $A_q$-valuation of $x(h) - \varepsilon(h)$ is $< 1$ for every $h \in H$, where $\varepsilon$ is the counit of $H$ composed with $\mathbb{Z}_{(q)} \to \overline{\mathbb{Q}}$; $\sigma \cdot e(x) - e(x) \in N$ for every $\sigma$ in that decomposition subgroup; and $x^{q^m} = 1$ for the convolution product. Then $e(x) \in N$.
--
--   This is the elimination step in the analysis of finite flat group schemes of multiplicative type: a point of $q$-power order whose coordinates all reduce to those of the identity, and whose displacements under the decomposition group at $q$ already lie in $N$, must itself be labelled inside $N$. It is used by [`GaloisRep.multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain`](thm.html#GaloisRep.multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain) to rule out trivial-type constituents inside the kernel of reduction at $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_label_mem_of_forall_decomposition_smul_sub_mem_of_finiteFlatHopf.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem GaloisRep.label_mem_of_forall_decomposition_smul_sub_mem_of_finiteFlatHopf
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt q) H]
    [Module.Finite (GaloisRep.ratLocalizedAt q) H] [Module.Flat (GaloisRep.ratLocalizedAt q) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt q) H]
    {J : Type} [AddCommGroup J] [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J]
    (M : AddSubgroup J) (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ) ≃ ↥M)
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ)),
      (∀ x : H, g x = σ (f x)) → ((e g : ↥M) : J) = σ • ((e f : ↥M) : J))
    (Aq : ValuationSubring (AlgebraicClosure ℚ)) (hAq : Aq.LiesOverPrime q)
    (m : ℕ)
    (N : AddSubgroup J)
    (hN : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ Aq.decompositionSubgroup ℚ → ∀ x ∈ N, σ • x ∈ N)
    (x : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ))
    (hred : ∀ h : H, Aq.valuation (x h - algebraMap (GaloisRep.ratLocalizedAt q) (AlgebraicClosure ℚ) (Coalgebra.counit h)) < 1)
    (hdisp : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ Aq.decompositionSubgroup ℚ →
      σ • ((e x : ↥M) : J) - ((e x : ↥M) : J) ∈ N)
    (htx : x ^ (q ^ m) = 1) :
    ((e x : ↥M) : J) ∈ N := by sorry
