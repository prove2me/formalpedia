-- Prove2me | Theorems.Thm_GaloisRep_finiteFlat_point_mem_of_valuation_sub_counit_lt_one_of_inertia_displacement_mem
-- name    : GaloisRep.finiteFlat_point_mem_of_valuation_sub_counit_lt_one_of_inertia_displacement_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/c59ac8e9-05ef-577b-a831-a8cf34c7e815
-- title:
--   Points reducing to the identity lie in inertia displacements (q odd)
-- statement:
--   Let $q$ be a prime with $q \neq 2$, and write $\mathbb{Z}_{(q)}$ for the subring [`GaloisRep.ratLocalizedAt q`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ consisting of the rationals whose denominator is coprime to $q$. Let $H$ be a commutative ring carrying the structure of a Hopf algebra over $\mathbb{Z}_{(q)}$ which is finite and flat as a $\mathbb{Z}_{(q)}$-module and whose comultiplication is cocommutative. Let $J$ be an additive commutative group with a distributive action of $\mathrm{Gal} = (\overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}})$, where $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, let $M \le J$ be an additive subgroup, and let $e$ be a bijection from `WithConv (H →ₐ[ℤ_(q)] ℚ̄)`, the $\overline{\mathbb{Q}}$-valued points of $H$ with the convolution product, onto $M$, such that $e(f\cdot g) = e(f) + e(g)$ for all points $f, g$, and such that whenever $g$ is the point with $g(x) = \sigma(f(x))$ for all $x \in H$ one has $e(g) = \sigma \cdot e(f)$ in $J$. Let $A_q$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $A_q$, and let $W \le J$ be an additive subgroup such that $\sigma \cdot x - x \in W$ for every $x \in M$ and every $\sigma$ in the image in $\mathrm{Gal}$ of the inertia subgroup of the decomposition subgroup of $A_q$ over $\mathbb{Q}$. Then for every point $f$ of $H$ such that the $A_q$-valuation of $f(h) - \varepsilon(h)$ is $< 1$ for all $h \in H$, where $\varepsilon$ is the counit of $H$ followed by $\mathbb{Z}_{(q)} \to \overline{\mathbb{Q}}$, the element $e(f) \in J$ lies in $W$.
--
--   This is the Raynaud-type input used at an odd auxiliary prime $q$: the points of a finite flat group scheme over $\mathbb{Z}_{(q)}$ that reduce to the identity at a place above $q$ cannot survive in any quotient on which inertia at $q$ acts trivially, so they are accounted for by inertia displacements. It feeds the computations of inertia invariants and of point counts in [`GaloisRepAdic.iSup_map_levelAction_sub_id_inf_eq_of_finiteFlat_level`](thm.html#GaloisRepAdic.iSup_map_levelAction_sub_id_inf_eq_of_finiteFlat_level) and [`GaloisRep.natCard_quotient_eq_natCard_ringHom_algClosure_of_finiteFlatHopf_of_multiplicativeTypeNat`](thm.html#GaloisRep.natCard_quotient_eq_natCard_ringHom_algClosure_of_finiteFlatHopf_of_multiplicativeTypeNat).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_finiteFlat_point_mem_of_valuation_sub_counit_lt_one_of_inertia_displacement_mem.lean

import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem GaloisRep.finiteFlat_point_mem_of_valuation_sub_counit_lt_one_of_inertia_displacement_mem
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
    (W : AddSubgroup J)
    (hcos : ∀ σ ∈ Aq.inertiaSubgroupIn ℚ, ∀ x ∈ M, σ • x - x ∈ W) :
    ∀ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ),
      (∀ h : H, Aq.valuation (f h
        - algebraMap (GaloisRep.ratLocalizedAt q) (AlgebraicClosure ℚ) (Coalgebra.counit h)) < 1) →
      ((e f : ↥M) : J) ∈ W := by sorry
