-- Prove2me | Theorems.Thm_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain_two
-- name    : GaloisRep.multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/671a2d29-cf7d-5d09-a37c-565275837763
-- title:
--   Reduction kernel is of multiplicative type at q=2
-- statement:
--   Let $q$ be a prime with $q=2$, and let $R=\mathbb{Z}_{(q)}$ be the subring [`GaloisRep.ratLocalizedAt q`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ consisting of the rationals whose denominator is coprime to $q$. Let $H$ be a commutative ring carrying a Hopf algebra structure over $R$ which is finite and flat as an $R$-module and whose comultiplication is cocommutative. Let $J$ be an abelian group with a distributive action of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, realised as the group of $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ`, let $M\le J$ be a subgroup, and let $e$ be a bijection from the convolution monoid `WithConv` of $R$-algebra homomorphisms $H\to\overline{\mathbb{Q}}$ onto $M$ such that $e(fg)=e(f)+e(g)$, and such that $e(g)=\sigma\cdot e(f)$ in $J$ whenever $g(x)=\sigma(f(x))$ for all $x\in H$. Let $A_q$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $A_q$, let $m\in\mathbb{N}$ and $n\colon\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})\to\mathbb{N}$ satisfy $\sigma\zeta=\zeta^{n(\sigma)}$ for every $\zeta$ with $\zeta^{q^m}=1$, and assume $q^m$ annihilates $M$. Let $M'\le M$ be a subgroup and $\mathrm{step}\colon \mathrm{Fin}(r+1)\to$ subgroups of $J$ a chain with $\mathrm{step}\,0=\bot$, $\mathrm{step}\,r=M'$, $\mathrm{step}\,i\le\mathrm{step}(i+1)$, every $\mathrm{step}\,i$ stable under the Galois action, each quotient $\mathrm{step}(i+1)/\mathrm{step}\,i$ of cardinality $q$, and each step admissible in the sense that either $\sigma\cdot x-x\in\mathrm{step}\,i$ for all $\sigma$ and all $x\in\mathrm{step}(i+1)$, or $\sigma\cdot x-n(\sigma)\cdot x\in\mathrm{step}\,i$ for all such $\sigma$ and $x$. Finally let $K\le M$ be the reduction kernel at $A_q$, characterised by: $e(f)\in K$ if and only if $A_q$-valuation of $f(h)-\varepsilon(h)$ is $<1$ for every $h\in H$, where $\varepsilon$ is the counit of $H$ followed by $R\to\overline{\mathbb{Q}}$. Then $K\sqcap M'$ is of multiplicative type for $n$ relative to the inertia subgroup of $A_q$ over $\mathbb{Q}$ (the image in the full Galois group of the inertia subgroup inside the decomposition subgroup): for every $\sigma$ in that inertia subgroup and every $x\in K\sqcap M'$ one has $\sigma\cdot x=n(\sigma)\cdot x$.
--
--   This is the $q=2$ instance of the statement that, for a finite flat commutative group scheme over $\mathbb{Z}_{(q)}$ with rational points identified with a Galois submodule $M$, inertia at $q$ acts on the part of the reduction kernel carried by an admissibly filtered subgroup $M'$ through the character $n$; the binders match those of the odd-$q$ companion, although at $q=2$ the two alternatives in the admissibility hypothesis coincide. It is used by [`ModularCurve.eisensteinTorsionBar_inertia_smul_sub_eq_nat_smul_two`](thm.html#ModularCurve.eisensteinTorsionBar_inertia_smul_sub_eq_nat_smul_two), [`ModularCurve.inertia_smul_eq_nsmul_of_mem_heckeTorsion_span_sup_of_reductionModL_eq_zero`](thm.html#ModularCurve.inertia_smul_eq_nsmul_of_mem_heckeTorsion_span_sup_of_reductionModL_eq_zero) and [`ModularCurve.multiplicativeTypeNat_inf_ker_reductionModL_eisensteinTorsionBar`](thm.html#ModularCurve.multiplicativeTypeNat_inf_ker_reductionModL_eisensteinTorsionBar) in the analysis of Eisenstein torsion on $J_0(p)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain_two.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_MultiplicativeType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem GaloisRep.multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain_two
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2)
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt q) H]
    [Module.Finite (GaloisRep.ratLocalizedAt q) H] [Module.Flat (GaloisRep.ratLocalizedAt q) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt q) H]
    {J : Type} [AddCommGroup J]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J]
    (M : AddSubgroup J)
    (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ) ≃ ↥M)
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) f g,
      (∀ x : H, g x = σ (f x)) → ((e g : ↥M) : J) = σ • ((e f : ↥M) : J))
    (Aq : ValuationSubring (AlgebraicClosure ℚ)) (hAq : Aq.LiesOverPrime q)
    (m : ℕ) (n : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → ℕ)
    (hn : ∀ σ, ∀ ζ : AlgebraicClosure ℚ, ζ ^ (q ^ m) = 1 → σ ζ = ζ ^ n σ)
    (htors : ∀ x : ↥M, q ^ m • x = 0)
    (M' : AddSubgroup J) (hM' : M' ≤ M)
    (r : ℕ) (step : Fin (r + 1) → AddSubgroup J) (hstep0 : step 0 = ⊥) (hstepr : step (Fin.last r) = M')
    (hmono : ∀ i : Fin r, step i.castSucc ≤ step i.succ)
    (hstab : ∀ i, ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ x ∈ step i, σ • x ∈ step i)
    (hcard : ∀ i : Fin r, Nat.card (↥(step i.succ) ⧸ (step i.castSucc).addSubgroupOf (step i.succ)) = q)
    (hadm : ∀ i : Fin r,
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ x ∈ step i.succ, σ • x - x ∈ step i.castSucc) ∨
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ x ∈ step i.succ, σ • x - n σ • x ∈ step i.castSucc))
    (K : AddSubgroup J) (hKM : K ≤ M)
    (hK : ∀ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ),
      ((e f : ↥M) : J) ∈ K ↔
        ∀ h : H, Aq.valuation (f h
          - algebraMap (GaloisRep.ratLocalizedAt q) (AlgebraicClosure ℚ) (Coalgebra.counit h)) < 1) :
    ModularCurve.MultiplicativeTypeNat (Aq.inertiaSubgroupIn ℚ) n (K ⊓ M') := by sorry
