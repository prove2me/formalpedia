-- Prove2me | Theorems.Thm_HeckeCohomology_heckeInvD_sub_card_smul
-- name    : HeckeCohomology.heckeInvD_sub_card_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/d4321244-0bee-5555-bb7a-405b1885a31c
-- title:
--   Degree-zero transfer Hecke operator is multiplication by the index
-- statement:
--   Let $k$ be a commutative ring, $M$ a natural number, $H$ a subgroup of $(\mathbb{Z}/M)^\times$, and $\ell$ a nonzero natural number. Write $\Gamma_H(M)$ for [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133), the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ obtained by pulling back $H$ along the lower-right-entry character $\Gamma_0(M)\to(\mathbb{Z}/M)^\times$ and transporting the result into $\mathrm{SL}_2(\mathbb{Z})$, and write $\Gamma_H(M)^{(\ell)}$ for [`CohCarrier.GammaHUpper M H ℓ`](def/CohCarrier_Level.html#L210), the subgroup of $\Gamma_H(M)$ cut out by the condition that the upper-right entry vanish modulo $\ell$. Let $A$ be a $k$-linear representation of $\Gamma_H(M)$ which is of diamond class in the sense of `IsDClass`, i.e. there is a representation $\theta$ of $(\mathbb{Z}/M)^\times$ on $A$ with $A.\rho(\gamma)=\theta(\mathrm{unitsOf}(\gamma))$ for every $\gamma$, and let $z$ lie in the $k$-submodule of $\Gamma_H(M)$-invariants of $A$. Then $\mathrm{heckeInvD}\,M\,H\,\ell\,A\,h_A$ applied to $z$, minus $n\cdot z$, is zero in the invariants, where $n$ is the cardinality of the set of right cosets of $\Gamma_H(M)^{(\ell)}$ in $\Gamma_H(M)$ (finite by the local finite-index instance). Equivalently, the degree-zero transfer Hecke operator acts on invariants as multiplication by the index $[\Gamma_H(M):\Gamma_H(M)^{(\ell)}]$.
--
--   This is the degree-zero case of the transfer description of Hecke operators on group cohomology: on $H^0$, where the cohomology is just the invariants and the twisting map is taken to be the identity, the operator collapses to the index of the level-raised subgroup. It is used in the analysis of eigensystems for $\Gamma_H(M)$-cohomology, being cited by [`CohCarrier.exists_diamondRaw_eq_heckeT_eq_smul_gammaH_bot_mul_or_eisenstein_of_isEigensystemH1_of_steinberg_quotient_of_four_le`](thm.html#CohCarrier.exists_diamondRaw_eq_heckeT_eq_smul_gammaH_bot_mul_or_eisenstein_of_isEigensystemH1_of_steinberg_quotient_of_four_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeCohomology_heckeInvD_sub_card_smul.lean

import Definitions.Def_GroupCohomology_DClassCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

theorem HeckeCohomology.heckeInvD_sub_card_smul {k : Type} [CommRing k] (M : ℕ)
    (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ] (A : Rep k ↥(CohCarrier.GammaH M H))
    (hA : IsDClass M H A) (z : A.ρ.invariants) :
    heckeInvD M H ℓ A hA z -
      Fintype.card (Quotient (QuotientGroup.rightRel (CohCarrier.GammaHUpper M H ℓ))) • z = 0 := by sorry
