-- Prove2me | Theorems.Thm_ModularCurve_XHDRLevel_valuationSubring_eq_gauss_or_eq_comap_atkinLehner_of_unique_of_relfinrank_gammaH
-- name    : ModularCurve.XHDRLevel.valuationSubring_eq_gauss_or_eq_comap_atkinLehner_of_unique_of_relfinrank_gammaH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/ee6feb8e-f517-5480-8a67-334a2bc7b335
-- title:
--   Only the Gauss branch and its Atkin–Lehner transform
-- statement:
--   Fix a prime $p$ and $M \ge 1$ with $p \mid M$ and $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing the kernel of the reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$; assume the $q$-expansion $j$ of the modular invariant lies in the field $F_{\mathrm{full}}$ generated over $\mathbb{Q}$ inside $\mathbb{Q}((q))$ by ratios of integral $q$-expansions of modular forms of equal weight on $\mathrm{SL}_2(\mathbb{Z})$. Write $F$ and $F'$ for the corresponding fields at levels $\Gamma_H(M)$ and $\Gamma_{H'}(M/p)$, $H'$ being the image of $H$, $j$ for the element of $F$ given by that $q$-expansion, and $R = \mathrm{ratLocalizedAt}\ p \subseteq \mathbb{Q}$ for the subring of rationals whose denominator is coprime to $p$. Let $\sigma$ be a $\mathbb{Q}$-algebra automorphism of $F$ which, on elements of $F$ whose Laurent series lies in $F'$, is given by $q \mapsto q^p$ (substitution of exponents by multiplication with $p$). Call a valuation subring $V$ of $F$ (or of $F'$) a branch ring if $R \subseteq V$, every element of the ideal $pR$ maps into the nonunits of $V$, and $Q(j), Q(j)^{-1} \in V$ for every $Q \in R[X]$ with nonzero reduction modulo $p$. Let $W_0$ be the valuation subring of $F$ consisting of the $f$ for which there are power series $a, a'$ over $R$ with $a'$ of nonzero reduction modulo $p$ and $f \cdot a' = a$ as Laurent series. Assume: $W_0$ is a branch ring in which $p$ divides every nonunit; the same holds for $W_0$ pulled back along $\sigma$, and these two subrings are distinct; any two branch rings of $F'$ are equal; and the relative degree $[F : F'] = p+1$. Then every branch ring $V$ of $F$ equals $W_0$ or equals the pullback of $W_0$ along $\sigma$.
--
--   In geometric terms this is the count of branches of the reduction at $p$ of $X_H(M)$ lying above the unique branch of $X_{H'}(M/p)$: there are exactly two, the Gauss branch and its image under the Atkin–Lehner substitution $q \mapsto q^p$, reflecting the Deligne–Rapoport description of the fibre at $p$ as two copies of the $j$-line. All valuation-theoretic inputs (the branch clauses for the two distinguished subrings, the uniqueness at level $M/p$ and the degree $p+1$) are hypotheses here, so that the statement isolates the counting step; it is used to prove the version of the same result in which those inputs are discharged.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRLevel_valuationSubring_eq_gauss_or_eq_comap_atkinLehner_of_unique_of_relfinrank_gammaH.lean

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

theorem ModularCurve.XHDRLevel.valuationSubring_eq_gauss_or_eq_comap_atkinLehner_of_unique_of_relfinrank_gammaH
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (σ : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ≃ₐ[ℚ] ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
    (hσ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) (u : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))),
        (f : LaurentSeries ℚ) = (u : LaurentSeries ℚ) →
          ((σ f : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) : LaurentSeries ℚ) = qExpand ℚ p (u : LaurentSeries ℚ))

    (W₀ : ValuationSubring ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
    (hW₀ : ∀ f : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)), f ∈ W₀ ↔
      ∃ a a' : PowerSeries ↥(GaloisRep.ratLocalizedAt p), a'.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 ∧
        (f : LaurentSeries ℚ) * HahnSeries.ofPowerSeries ℤ ℚ (a'.map (GaloisRep.ratLocalizedAt p).subtype) =
          HahnSeries.ofPowerSeries ℤ ℚ (a.map (GaloisRep.ratLocalizedAt p).subtype))
    (hW₀₁ : ∀ a : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ W₀)
    (hW₀₁' : ∀ a ∈ Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))}, algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ (W₀).nonunits)
    (hW₀₂ : ∀ Q : Polynomial ↥(GaloisRep.ratLocalizedAt p), Q.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 →
      Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q ∈ W₀ ∧ (Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q)⁻¹ ∈ W₀)
    (hW₀₆ : ∀ x : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)), x ∈ (W₀).nonunits → x * (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)))⁻¹ ∈ W₀)

    (hW₁₁ : ∀ a : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ (W₀.comap σ.toAlgHom.toRingHom))
    (hW₁₁' : ∀ a ∈ Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))}, algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ ((W₀.comap σ.toAlgHom.toRingHom)).nonunits)
    (hW₁₂ : ∀ Q : Polynomial ↥(GaloisRep.ratLocalizedAt p), Q.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 →
      Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q ∈ (W₀.comap σ.toAlgHom.toRingHom) ∧ (Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q)⁻¹ ∈ (W₀.comap σ.toAlgHom.toRingHom))
    (hW₁₆ : ∀ x : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)), x ∈ ((W₀.comap σ.toAlgHom.toRingHom)).nonunits → x * (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)))⁻¹ ∈ (W₀.comap σ.toAlgHom.toRingHom))
    (hne : (W₀.comap σ.toAlgHom.toRingHom) ≠ W₀)

    (huniq : ∀ V V' : ValuationSubring ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))),
      (∀ a : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) a ∈ V) →
        (∀ a ∈ Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))}, algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) a ∈ (V).nonunits) →
        (∀ Q : Polynomial ↥(GaloisRep.ratLocalizedAt p), Q.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 →
          Polynomial.aeval (jAt (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) hj) Q ∈ V ∧ (Polynomial.aeval (jAt (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) hj) Q)⁻¹ ∈ V) →
      (∀ a : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) a ∈ V') →
        (∀ a ∈ Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))}, algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) a ∈ (V').nonunits) →
        (∀ Q : Polynomial ↥(GaloisRep.ratLocalizedAt p), Q.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 →
          Polynomial.aeval (jAt (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) hj) Q ∈ V' ∧ (Polynomial.aeval (jAt (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) hj) Q)⁻¹ ∈ V') →
        V = V')

    (hdeg : IntermediateField.relfinrank (qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))
      (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) = p + 1)

    (V : ValuationSubring ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
    (hV₁ : ∀ a : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ V)
    (hV₁' : ∀ a ∈ Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))}, algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ V.nonunits)
    (hV₂ : ∀ Q : Polynomial ↥(GaloisRep.ratLocalizedAt p), Q.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 →
      Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q ∈ V ∧ (Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q)⁻¹ ∈ V) :
    V = W₀ ∨ V = W₀.comap σ.toAlgHom.toRingHom := by sorry
