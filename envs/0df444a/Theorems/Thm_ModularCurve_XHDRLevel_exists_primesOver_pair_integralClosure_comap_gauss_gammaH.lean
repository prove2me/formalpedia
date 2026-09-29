-- Prove2me | Theorems.Thm_ModularCurve_XHDRLevel_exists_primesOver_pair_integralClosure_comap_gauss_gammaH
-- name    : ModularCurve.XHDRLevel.exists_primesOver_pair_integralClosure_comap_gauss_gammaH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/67648209-87b4-55ec-85db-0bf8fd2e4d6c
-- title:
--   Two primes over the Gauss ring with residue degrees 1 and p
-- statement:
--   Let $p$ be a prime and $M\neq 0$ with $p\mid M$ but $p^2\nmid M$, and let $H\le(\mathbb{Z}/M)^\times$ contain every unit whose image under `ZMod.unitsMap` for $M/p\mid M$ is $1$. Write $\Gamma_H(M)$ for the image in $\mathrm{SL}_2(\mathbb{Z})$ of the preimage of $H$ under the lower-right-entry character of $\Gamma_0(M)$, $H'$ for the image of $H$ in $(\mathbb{Z}/(M/p))^\times$, and $F=$ `qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)`, $E=$ `qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))` for the subfields of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by ratios of integral $q$-expansions of modular forms of the respective levels; assume $j=$ `jqModC ℚ` lies in the level-one such field, and $E\le F$. Let $\sigma$ be a $\mathbb{Q}$-algebra automorphism of $F$ sending each element of $F$ whose Laurent series equals that of some $u\in E$ to `qExpand ℚ p` of that series, i.e. $u(q)\mapsto u(q^p)$. Let $W_0$ be a valuation subring of $F$ whose elements are exactly the $f$ with $f\cdot a'=a$ for power series $a,a'$ over $R=$ [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) (rationals with denominator coprime to $p$) with $a'$ of nonzero reduction under [`GaloisRep.ratLocalizedAtResidue p`](def/GaloisRep_RatLocalizedAtResidue.html#L15). Assume of $W_0$, and likewise of $W_1=\{x\mid\sigma x\in W_0\}$: it contains the image of $R$; the image of the ideal $(p)$ consists of nonunits; $Q(j)$ and $Q(j)^{-1}$ lie in it for every $Q\in R[X]$ of nonzero reduction; and $x\cdot p^{-1}$ lies in it for every nonunit $x$. Assume $W_1\neq W_0$. Then, with $\iota:E\to F$ the inclusion and $V'=W_0\cap E$ its comap, the integral closure of $V'$ in $F$ carries two distinct nonzero prime ideals $\mathfrak{P}_0,\mathfrak{P}_1$, both lying over the maximal ideal of $V'$, with `inertiaDeg'` at least $1$ and at least $p$ respectively.
--
--   This is the modular input to the branch count at a level divisible exactly once by $p$: the centres in the integral closure of the two branch rings $W_0$ (the Gauss ring) and $W_1=\sigma^{-1}(W_0)$ are distinct primes over the maximal ideal of $W_0\cap E$, carrying residue degrees at least $1$ and at least $p$. Together with $[F:E]=p+1$ it is used by [`ModularCurve.XHDRLevel.valuationSubring_eq_gauss_or_eq_comap_atkinLehner_of_unique_of_relfinrank_gammaH`](thm.html#ModularCurve.XHDRLevel.valuationSubring_eq_gauss_or_eq_comap_atkinLehner_of_unique_of_relfinrank_gammaH) to show that every valuation ring of $F$ dominating $W_0\cap E$ is one of these two.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRLevel_exists_primesOver_pair_integralClosure_comap_gauss_gammaH.lean

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

theorem ModularCurve.XHDRLevel.exists_primesOver_pair_integralClosure_comap_gauss_gammaH
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))

    (hEF : qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) ≤ qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))
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
    (hne : (W₀.comap σ.toAlgHom.toRingHom) ≠ W₀) :
    let ι : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) →+* ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) := (IntermediateField.inclusion hEF : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) →+* ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
    letI : Algebra ↥(W₀.comap ι) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) := (ι.comp (W₀.comap ι).subtype).toAlgebra
    ∃ 𝔓₀ 𝔓₁ : Ideal ↥(integralClosure ↥(W₀.comap ι) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))),
      𝔓₀.IsPrime ∧ 𝔓₁.IsPrime ∧ 𝔓₀ ≠ ⊥ ∧ 𝔓₁ ≠ ⊥ ∧ 𝔓₀ ≠ 𝔓₁ ∧
      𝔓₀.LiesOver (IsLocalRing.maximalIdeal ↥(W₀.comap ι)) ∧ 𝔓₁.LiesOver (IsLocalRing.maximalIdeal ↥(W₀.comap ι)) ∧
      1 ≤ (IsLocalRing.maximalIdeal ↥(W₀.comap ι)).inertiaDeg' 𝔓₀ ∧
      p ≤ (IsLocalRing.maximalIdeal ↥(W₀.comap ι)).inertiaDeg' 𝔓₁ := by sorry
