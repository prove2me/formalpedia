-- Prove2me | Theorems.Thm_ModularCurve_XHDRLevel_exists_valuationSubring_pair_gammaH
-- name    : ModularCurve.XHDRLevel.exists_valuationSubring_pair_gammaH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/33643d95-af40-52d7-8d3c-8d374038ad4a
-- title:
--   Exactly two branch valuation rings of F(Γ_H(M)) above j mod p
-- statement:
--   Let $p$ be a prime, $M$ a nonzero natural number, $H$ a subgroup of $(\mathbb{Z}/M)^\times$, and assume $p \mid M$ but $p^2 \nmid M$ and that every unit $u$ of $\mathbb{Z}/M$ whose image under the reduction map $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ is $1$ lies in $H$. Assume also that the Laurent series $\mathtt{jqModC}\,\mathbb{Q} = q^{-1}E_4^3\eta^{-24}$ lies in $F(\mathrm{SL}_2(\mathbb{Z})) =$ the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the quotients $p_f/p_g$ of integral $q$-expansions of modular forms of equal weight on the full group. Write $F$ for the corresponding field $F(\Gamma_H(M))$ attached to $\Gamma_H(M)$, the image in $\mathrm{SL}_2(\mathbb{Z})$ of the preimage of $H$ under the character $\Gamma_0(M) \to (\mathbb{Z}/M)^\times$, $j \in F$ for that Laurent series viewed in $F$, and $R \subseteq \mathbb{Q}$ for the subring of rationals whose denominator is coprime to $p$, with its residue map $R \to \mathbb{Z}/p$. Then there exist two valuation subrings $W_0, W_1$ of $F$ such that, for $i = 0, 1$: $R$ maps into $W_i$ and every element of the ideal $(p)$ of $R$ maps into the nonunits of $W_i$; for every polynomial $Q$ over $R$ whose reduction modulo $p$ is nonzero, both $Q(j)$ and $Q(j)^{-1}$ lie in $W_i$; moreover $W_0 \neq W_1$, every valuation subring $V$ of $F$ with these three properties equals $W_0$ or $W_1$, and every nonunit $x$ of $W_i$ satisfies $x p^{-1} \in W_i$.
--
--   The valuation subrings described are the branches of the reduction of $X_H(M)$ modulo $p$ lying above the generic point of the $j$-line, and the statement says there are exactly two of them, each with $p$ generating its maximal ideal; classically these correspond to the two Igusa components of $X_0(p)$ in characteristic $p$ (Deligne–Rapoport, Katz–Mazur). It packages the hypotheses required by the dictionary between such branch rings and the minimal primes over $(p)$ in a two-chart integral model, and is used downstream in the construction of the pair of Laurent-series chart maps for $X_H(M)$ at $p$ and in identifying the associated components.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRLevel_exists_valuationSubring_pair_gammaH.lean

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

theorem ModularCurve.XHDRLevel.exists_valuationSubring_pair_gammaH
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) :
    ∃ W₀ W₁ : ValuationSubring ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)),

      (∀ i : Fin 2, (∀ a : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ (![W₀, W₁] i)) ∧
        ∀ a ∈ Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))}, algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ (![W₀, W₁] i).nonunits) ∧

      (∀ i : Fin 2, ∀ Q : Polynomial ↥(GaloisRep.ratLocalizedAt p), Q.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 →
        Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q ∈ (![W₀, W₁] i) ∧ (Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q)⁻¹ ∈ (![W₀, W₁] i)) ∧

      W₀ ≠ W₁ ∧

      (∀ V : ValuationSubring ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)),
        (∀ a : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ V) →
        (∀ a ∈ Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))}, algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ V.nonunits) →
        (∀ Q : Polynomial ↥(GaloisRep.ratLocalizedAt p), Q.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 →
          Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q ∈ V ∧ (Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q)⁻¹ ∈ V) →
        V = W₀ ∨ V = W₁) ∧

      (∀ i : Fin 2, ∀ x : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)), x ∈ (![W₀, W₁] i).nonunits →
        x * (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)))⁻¹ ∈ (![W₀, W₁] i)) := by sorry
