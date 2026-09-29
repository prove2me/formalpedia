-- Prove2me | Theorems.Thm_ModularCurve_XHDRLevel_comap_atkinLehner_valuationSubring_gauss_gammaH
-- name    : ModularCurve.XHDRLevel.comap_atkinLehner_valuationSubring_gauss_gammaH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/7c1097a6-df9a-531a-9b3d-a31e34608869
-- title:
--   Atkin–Lehner pullback of the Gauss ring is a distinct branch ring
-- statement:
--   Let $p$ be a prime and $M$ a nonzero natural number with $p \mid M$ and $p^2 \nmid M$, and let $H \le (\mathbb{Z}/M)^\times$ be a subgroup containing every unit $u$ whose image under the reduction map $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ is $1$. Write $F_\Gamma := \mathtt{qExpFunctionFieldC}\,\mathbb{Q}\,\Gamma$ for the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the quotients $f/g$ of integral $q$-expansions of modular forms of a common weight on $\Gamma$, and put $F := F_{\Gamma_H(M)}$ where $\Gamma_H(M)$ is the image in $\mathrm{SL}_2(\mathbb{Z})$ of the preimage of $H$ under the determinant-type character $\Gamma_0(M) \to (\mathbb{Z}/M)^\times$. Assume the $q$-expansion $j = q^{-1}\cdot(\text{integral power series})$, namely `jqModC`, lies in $F_{\mathrm{SL}_2(\mathbb{Z})}$; let $j$ also denote its image `jAt` in $F$. Let $\sigma$ be a $\mathbb{Q}$-algebra automorphism of $F$ such that, whenever $f \in F$ has the same underlying Laurent series as an element $u$ of $F_{\Gamma_{H'}(M/p)}$, with $H'$ the image of $H$ in $(\mathbb{Z}/(M/p))^\times$, the series of $\sigma f$ is $u(q^p)$ (substitution $q \mapsto q^p$, i.e. `qExpand`). Write $R := \mathtt{ratLocalizedAt}\,p$, the subring of rationals with denominator coprime to $p$, and let reduction $R \to \mathbb{Z}/p$ be `ratLocalizedAtResidue`. Let $W_0$ be a valuation subring of $F$ consisting exactly of those $f$ for which there are power series $a, a'$ over $R$ with $a'$ of nonzero reduction mod $p$ and $f \cdot a' = a$ as Laurent series. Then the pullback $W_1 := \sigma^{-1}(W_0)$ satisfies: $R$ maps into $W_1$ and the ideal $(p)$ of $R$ maps into the nonunits of $W_1$; for every $Q \in R[X]$ with nonzero reduction mod $p$, both $Q(j)$ and $Q(j)^{-1}$ lie in $W_1$; every nonunit $x$ of $W_1$ satisfies $x p^{-1} \in W_1$; and $W_1 \ne W_0$.
--
--   This provides the second of the two branch rings of $F(\Gamma_H(M))$ above the generic point of the $j$-line in characteristic $p$, obtained by transporting the Gauss ring $W_0$ along the Atkin–Lehner-type substitution $q \mapsto q^p$, together with the assertion that the two branches are distinct. It is used in the construction of the branch pair for $X_H(M)$ at $p$ and in the subsequent analysis of the special fibre of the model, where the two branches correspond to the two Igusa components.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRLevel_comap_atkinLehner_valuationSubring_gauss_gammaH.lean

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

theorem ModularCurve.XHDRLevel.comap_atkinLehner_valuationSubring_gauss_gammaH
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
          HahnSeries.ofPowerSeries ℤ ℚ (a.map (GaloisRep.ratLocalizedAt p).subtype)) :
    ((∀ a : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ W₀.comap σ.toAlgHom.toRingHom) ∧
        ∀ a ∈ Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))}, algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ (W₀.comap σ.toAlgHom.toRingHom).nonunits) ∧
      (∀ Q : Polynomial ↥(GaloisRep.ratLocalizedAt p), Q.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 →
        Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q ∈ W₀.comap σ.toAlgHom.toRingHom ∧ (Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q)⁻¹ ∈ W₀.comap σ.toAlgHom.toRingHom) ∧
      (∀ x : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)), x ∈ (W₀.comap σ.toAlgHom.toRingHom).nonunits →
        x * (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)))⁻¹ ∈ W₀.comap σ.toAlgHom.toRingHom) ∧
      W₀.comap σ.toAlgHom.toRingHom ≠ W₀ := by sorry
