-- Prove2me | Theorems.Thm_ModularCurve_XHDRLevel_valuationSubring_unique_gammaH_infSubgroup_of_not_sq_dvd
-- name    : ModularCurve.XHDRLevel.valuationSubring_unique_gammaH_infSubgroup_of_not_sq_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/ec8dcdfc-fac5-5acf-b190-8df48a310ed5
-- title:
--   Uniqueness of the branch ring at p for Γ_{H'}(M/p)
-- statement:
--   Fix a prime $p$ and a nonzero natural number $M$ with $p \mid M$ but $p^2 \nmid M$, and let $H \le (\mathbb{Z}/M)^\times$ be a subgroup containing every unit $u$ whose image under the reduction $\mathrm{ZMod.unitsMap}\colon (\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ is trivial. Assume the $q$-series $j_q = q^{-1}\cdot(E_4^3\,\eta^{-24})$ over $\mathbb{Q}$ lies in the level-one $q$-expansion function field, i.e. in the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the ratios of integral $q$-expansions of pairs of modular forms of equal weight on $SL(2,\mathbb{Z})$. Write $H'$ for the image of $H$ in $(\mathbb{Z}/(M/p))^\times$, $\Gamma_{H'}(M/p) \le SL(2,\mathbb{Z})$ for the image of the preimage of $H'$ under the lower-right-entry character $\Gamma_0(M/p) \to (\mathbb{Z}/(M/p))^\times$, $F$ for the corresponding $q$-expansion function field over $\mathbb{Q}$, $j \in F$ for the element given by $j_q$, and $R \subseteq \mathbb{Q}$ for the subring of rationals whose denominator is coprime to $p$. Let $V, V'$ be valuation subrings of $F$ such that each contains the image of $R$, sends every element of the ideal $(p) \subseteq R$ into its nonunits, and satisfies $Q(j) \in V$ and $Q(j)^{-1} \in V$ (respectively for $V'$) for every $Q \in R[X]$ whose reduction along $R \to \mathbb{Z}/p$ is nonzero. Then $V = V'$.
--
--   This is the function-field form of the statement that at a prime $p$ not dividing the level $M/p$ the modular curve $X_{H'}(M/p)$ has irreducible reduction (Deuring–Igusa), so that only one valuation of its function field restricts to the Gauss valuation of $\mathbb{Q}(j)$ at $p$. It is used in the analysis of the two-chart integral model at $p$ in the case $p \parallel M$, in particular to identify the valuation rings of $F(\Gamma_H(M))$ above $p$ with the Gauss ring and its Atkin–Lehner conjugate, and to compute the pair of primes above $p$ in the relevant integral closure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRLevel_valuationSubring_unique_gammaH_infSubgroup_of_not_sq_dvd.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_GaloisRep_RatLocalizedAtResidue

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.XHDRLevel.valuationSubring_unique_gammaH_infSubgroup_of_not_sq_dvd
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (V V' : ValuationSubring ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))) :
    (∀ a : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) a ∈ V) →
        (∀ a ∈ Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))}, algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) a ∈ (V).nonunits) →
        (∀ Q : Polynomial ↥(GaloisRep.ratLocalizedAt p), Q.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 →
          Polynomial.aeval (jAt (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) hj) Q ∈ V ∧ (Polynomial.aeval (jAt (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) hj) Q)⁻¹ ∈ V) →
    (∀ a : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) a ∈ V') →
        (∀ a ∈ Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))}, algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) a ∈ (V').nonunits) →
        (∀ Q : Polynomial ↥(GaloisRep.ratLocalizedAt p), Q.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 →
          Polynomial.aeval (jAt (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) hj) Q ∈ V' ∧ (Polynomial.aeval (jAt (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) hj) Q)⁻¹ ∈ V') →
      V = V' := by sorry
