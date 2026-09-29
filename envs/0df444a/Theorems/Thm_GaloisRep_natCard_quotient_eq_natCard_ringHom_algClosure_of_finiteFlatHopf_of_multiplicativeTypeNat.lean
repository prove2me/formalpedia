-- Prove2me | Theorems.Thm_GaloisRep_natCard_quotient_eq_natCard_ringHom_algClosure_of_finiteFlatHopf_of_multiplicativeTypeNat
-- name    : GaloisRep.natCard_quotient_eq_natCard_ringHom_algClosure_of_finiteFlatHopf_of_multiplicativeTypeNat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/183b9a79-f73c-596c-a9a8-f70054df0a52
-- title:
--   Multiplicative-type quotient counts 𝔽̄_q-points of a finite flat Hopf algebra
-- statement:
--   Let $q$ be a prime with $q \neq 2$, and write $\mathbb{Z}_{(q)}$ for the subring [`GaloisRep.ratLocalizedAt q`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ consisting of the rationals whose denominator is coprime to $q$. Let $H$ be a commutative ring carrying a cocommutative Hopf algebra structure over $\mathbb{Z}_{(q)}$ which is finite and flat as a $\mathbb{Z}_{(q)}$-module. Let $J$ be an abelian group with a distributive action of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) = (\overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}})$, let $M \le J$ be a subgroup, and let $e$ be a bijection from the type of $\mathbb{Z}_{(q)}$-algebra homomorphisms $H \to \overline{\mathbb{Q}}$, with its convolution product, onto $M$, such that $e(f\cdot g) = e f + e g$ and such that whenever $g = \sigma \circ f$ pointwise on $H$ one has $e g = \sigma \cdot e f$ in $J$. Let $A_q$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q$ in its non-units, let $m \in \mathbb{N}$ and $n : \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) \to \mathbb{N}$ satisfy $\sigma\zeta = \zeta^{n\sigma}$ for every $\zeta$ with $\zeta^{q^m} = 1$, and suppose $q^m$ kills $M$. Let $W \le M$ be a subgroup such that $\sigma \cdot x = (n\sigma) \cdot x$ for all $x \in W$ and all $\sigma$ in the inertia subgroup of $A_q$ over $\mathbb{Q}$ (the image of `inertiaSubgroup` inside the Galois group), and such that $\sigma \cdot x - x \in W$ for all such $\sigma$ and all $x \in M$. Then the order of $M/W$ equals the number of ring homomorphisms $H \to \overline{\mathbb{F}}_q$.
--
--   In the classical language this says that for a finite flat commutative group scheme over $\mathbb{Z}_{(q)}$ at an odd prime $q$, a subgroup $W$ of the group of $\overline{\mathbb{Q}}$-points which is of multiplicative type for inertia at $q$ and absorbs all inertia displacements is exactly the group of points of the connected component, so that $M/W$ has the order of the étale quotient, i.e. the number of geometric points of the special fibre. It feeds the computation of the Eisenstein-primary torsion quotient in [`ModularCurve.natCard_eisensteinPrimaryTorsionBar_quotient_eq_pow_alpha_of_multiplicativeTypeNat`](thm.html#ModularCurve.natCard_eisensteinPrimaryTorsionBar_quotient_eq_pow_alpha_of_multiplicativeTypeNat).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_natCard_quotient_eq_natCard_ringHom_algClosure_of_finiteFlatHopf_of_multiplicativeTypeNat.lean

import Definitions.Def_GaloisRep_Flat
import Definitions.Def_ModularCurve_MultiplicativeType
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem GaloisRep.natCard_quotient_eq_natCard_ringHom_algClosure_of_finiteFlatHopf_of_multiplicativeTypeNat
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
    (W : AddSubgroup J) (hWM : W ≤ M)
    (hμ : ModularCurve.MultiplicativeTypeNat (Aq.inertiaSubgroupIn ℚ) n W)
    (hcos : ∀ σ ∈ Aq.inertiaSubgroupIn ℚ, ∀ x ∈ M, σ • x - x ∈ W) :
    Nat.card (↥M ⧸ W.addSubgroupOf M) = Nat.card (H →+* AlgebraicClosure (ZMod q)) := by sorry
