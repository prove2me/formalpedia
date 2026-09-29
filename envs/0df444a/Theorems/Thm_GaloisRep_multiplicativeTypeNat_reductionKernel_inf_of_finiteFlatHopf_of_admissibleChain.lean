-- Prove2me | Theorems.Thm_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain
-- name    : GaloisRep.multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/1bf13c84-d867-51a2-9ee4-154387ecbb33
-- title:
--   Inertia acts on admissible reduction kernels via n
-- statement:
--   Let $q$ be an odd prime and let $H$ be a commutative ring carrying a Hopf algebra structure over the subring $\mathbb{Z}_{(q)} =$ [`GaloisRep.ratLocalizedAt q`](def/GaloisRep_Flat.html#L8) of rationals whose denominator is coprime to $q$, which is finite and flat as a $\mathbb{Z}_{(q)}$-module and whose comultiplication is cocommutative. Let $J$ be an additive abelian group with a distributive action of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, let $M \le J$ be a subgroup, and let $e$ be a bijection from the monoid `WithConv` of $\mathbb{Z}_{(q)}$-algebra homomorphisms $H \to \overline{\mathbb{Q}}$ under convolution onto $M$ such that $e(fg) = e(f) + e(g)$, and such that $e(g) = \sigma \cdot e(f)$ in $J$ whenever $g(x) = \sigma(f(x))$ for all $x \in H$. Let $A_q$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $A_q$. Let $m \in \mathbb{N}$ and $n \colon \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) \to \mathbb{N}$ satisfy $\sigma(\zeta) = \zeta^{n(\sigma)}$ for every $\sigma$ and every $\zeta$ with $\zeta^{q^m} = 1$, and suppose $q^m \cdot x = 0$ for all $x \in M$. Let $M' \le M$, and let $\mathrm{step} \colon \mathrm{Fin}(r+1) \to$ subgroups of $J$ satisfy $\mathrm{step}(0) = 0$, $\mathrm{step}(r) = M'$, $\mathrm{step}(i) \le \mathrm{step}(i+1)$, each $\mathrm{step}(i)$ stable under the Galois action, each quotient $\mathrm{step}(i+1)/\mathrm{step}(i)$ of cardinality $q$, and each step admissible in the sense that either $\sigma x - x \in \mathrm{step}(i)$ for all $\sigma$ and all $x \in \mathrm{step}(i+1)$, or $\sigma x - n(\sigma) x \in \mathrm{step}(i)$ for all such $\sigma, x$. Finally let $K \le M$ satisfy: $e(f) \in K$ if and only if the $A_q$-valuation of $f(h) - \varepsilon(h)$ is $< 1$ for every $h \in H$, where $\varepsilon$ is the counit of $H$ composed with $\mathbb{Z}_{(q)} \to \overline{\mathbb{Q}}$. Then for every $\sigma$ in the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A_q$ over $\mathbb{Q}$ and every $x \in K \cap M'$ one has $\sigma \cdot x = n(\sigma) \cdot x$.
--
--   This is the local half of Mazur's ordinariness statement at an odd prime $q$: the connected part of an admissibly filtered finite flat commutative group scheme over $\mathbb{Z}_{(q)}$, here presented through its Hopf algebra $H$, its $\overline{\mathbb{Q}}$-points identified with $M$, and the reduction kernel $K$ at a place $A_q$ above $q$, is of multiplicative type, inertia acting through the chosen lift $n$ of the mod $q^m$ cyclotomic character. It is used in the analysis of the Galois action on torsion of modular Jacobians, via [`ModularCurve.eisensteinTorsionBar_inertia_smul_sub_eq_nat_smul`](thm.html#ModularCurve.eisensteinTorsionBar_inertia_smul_sub_eq_nat_smul) and [`ModularCurve.inertia_smul_eq_nsmul_of_mem_heckeTorsion_span_sup_of_reductionModL_eq_zero`](thm.html#ModularCurve.inertia_smul_eq_nsmul_of_mem_heckeTorsion_span_sup_of_reductionModL_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_MultiplicativeType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem GaloisRep.multiplicativeTypeNat_reductionKernel_inf_of_finiteFlatHopf_of_admissibleChain
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
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
