-- Prove2me | Theorems.Thm_ModularCurve_XHDRLevel_valuationSubring_eq_gauss_or_eq_comap_atkinLehner_gammaH
-- name    : ModularCurve.XHDRLevel.valuationSubring_eq_gauss_or_eq_comap_atkinLehner_gammaH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/5d2dfd9f-f0f9-5120-a640-ff654b8cfa06
-- title:
--   No third branch above the Gauss point for Γ_H(M)
-- statement:
--   Fix a prime $p$ and $M \ge 1$ with $M \neq 0$, a subgroup $H \le (\mathbb{Z}/M)^{\times}$, and assume $p \mid M$ but $p^2 \nmid M$ and that every unit of $\mathbb{Z}/M$ whose image under the reduction $(\mathbb{Z}/M)^{\times} \to (\mathbb{Z}/(M/p))^{\times}$ is trivial lies in $H$. Write $F =$ `qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)`, the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the quotients of integral $q$-expansions of two modular forms of equal weight for $\Gamma_H(M)$ (the group obtained by pulling $H$ back along $\Gamma_0(M) \to (\mathbb{Z}/M)^{\times}$, $\gamma \mapsto \gamma_{11} \bmod M$, and including into $SL_2(\mathbb{Z})$), and assume the Laurent series $j = q^{-1}\cdot(E_4^3 \cdot \eta\text{-unit})$ lies in the corresponding field for $SL_2(\mathbb{Z})$, so that it determines an element $j$ of $F$. Let $\sigma$ be a $\mathbb{Q}$-algebra automorphism of $F$ satisfying the Atkin–Lehner law: whenever $f \in F$ has the same Laurent expansion as an element $u$ of the field attached to $\Gamma_{H'}(M/p)$, $H'$ the image of $H$ in $(\mathbb{Z}/(M/p))^{\times}$, then $\sigma(f)$ expands as $u(q^p)$. Let $R \subseteq \mathbb{Q}$ be the subring of rationals with denominator coprime to $p$, and let $W_0$ be a valuation subring of $F$ whose elements are exactly the $f$ for which there are power series $a, a'$ over $R$ with $a' \not\equiv 0$ modulo $p$ and $f \cdot a' = a$ in $\mathbb{Q}((q))$. Then any valuation subring $V$ of $F$ that contains the image of $R$, has every element of $pR$ mapping into its nonunits, and contains $Q(j)$ together with $Q(j)^{-1}$ for every $Q \in R[X]$ with nonzero reduction modulo $p$, satisfies $V = W_0$ or $V = \sigma^{-1}(W_0)$, the preimage of $W_0$ under $\sigma$.
--
--   This is the "no third component" half of the classical description of the reduction of $X_H(M)$ at a prime $p$ exactly dividing $M$: the valuation rings of the function field extending the Gauss valuation of $\mathbb{Q}(j)$ are precisely the Gauss ring and its Atkin–Lehner transform, corresponding to the two components of the special fibre. It is used in the construction of the pair of such valuation rings and in the analysis of the minimal primes and of the fibres of the model of $X_H(M)$ at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRLevel_valuationSubring_eq_gauss_or_eq_comap_atkinLehner_gammaH.lean

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

theorem ModularCurve.XHDRLevel.valuationSubring_eq_gauss_or_eq_comap_atkinLehner_gammaH
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

    (V : ValuationSubring ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
    (hV₁ : ∀ a : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ V)
    (hV₁' : ∀ a ∈ Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))}, algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ V.nonunits)
    (hV₂ : ∀ Q : Polynomial ↥(GaloisRep.ratLocalizedAt p), Q.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 →
      Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q ∈ V ∧ (Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q)⁻¹ ∈ V) :
    V = W₀ ∨ V = W₀.comap σ.toAlgHom.toRingHom := by sorry
