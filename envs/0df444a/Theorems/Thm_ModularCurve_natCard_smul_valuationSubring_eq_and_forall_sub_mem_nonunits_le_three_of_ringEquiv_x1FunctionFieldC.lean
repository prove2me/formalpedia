-- Prove2me | Theorems.Thm_ModularCurve_natCard_smul_valuationSubring_eq_and_forall_sub_mem_nonunits_le_three_of_ringEquiv_x1FunctionFieldC
-- name    : ModularCurve.natCard_smul_valuationSubring_eq_and_forall_sub_mem_nonunits_le_three_of_ringEquiv_x1FunctionFieldC
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/4f6de816-24fb-5093-80bf-9f68eac27c45
-- title:
--   Inertia at a j-integral place of κ(X₁(M)) has order at most 3
-- statement:
--   Let $p$ be a prime with $p \ge 5$, let $M$ be a nonzero natural number with $M \ge 5$ and $p \nmid M$, and let $\kappa$ be a finite field of characteristic $p$. Let $F$ be a field equipped with a $\kappa$-algebra structure, and let $\theta : F \to \;$[`ModularCurve.x1FunctionFieldC κ M`](def/ModularCurve_X1.html#L134) be a ring isomorphism onto the intermediate field of the Laurent series field over $\kappa$ generated over $\kappa$ by the set [`ModularCurve.intFormRatiosC κ (Gamma1 M)`](def/ModularCurve_X1.html#L83), assumed to commute with the structural maps from $\kappa$ on both sides. Let $J \in F$ be an element whose image under $\theta$ has, as a Laurent series, the $q$-expansion [`ModularCurve.jqModC κ`](def/ModularCurve_JqCoeff.html#L15), namely $q^{-1}$ times the reduction to $\kappa$ of the integral power series $E_4^3 \cdot$ `dedekindEtaUnitInv`. Let $G$ be a finite group acting on $F$ by ring automorphisms, the action being faithful, fixing every element of the image of $\kappa$ and fixing $J$. Let $P$ be a valuation subring of $F$ containing the image of $\kappa$, with $P \ne \top$, with $P$ a principal ideal ring, and with $J \in P$. Then the number of $g \in G$ such that $g \cdot P = P$ and $g\cdot e - e$ is a nonunit of $P$ for every $e \in P$ is at most $3$.
--
--   This is the tame ramification bound at a place of the function field of $X_1(M)$ in characteristic $p \ge 5$ at which $j$ is integral: the displayed subgroup is the inertia group of $P$ for the $G$-action, and its order is bounded by the $j$-width at the corresponding geometric point, which lies in $\{1,2,3\}$ when $p \ge 5$. It is used in the analysis of the integral model of $X_1(M) \to X_0(p)$, in [`ModularCurve.XOneGammaZeroP.card_inertia_le_three_of_mem_ssJSet_twoChartIntegralModel_x1x0_gamma0_of_five_le`](thm.html#ModularCurve.XOneGammaZeroP.card_inertia_le_three_of_mem_ssJSet_twoChartIntegralModel_x1x0_gamma0_of_five_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_natCard_smul_valuationSubring_eq_and_forall_sub_mem_nonunits_le_three_of_ringEquiv_x1FunctionFieldC.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Pointwise

theorem ModularCurve.natCard_smul_valuationSubring_eq_and_forall_sub_mem_nonunits_le_three_of_ringEquiv_x1FunctionFieldC
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (κ : Type) [Field κ] [CharP κ p] [Finite κ]
    (F : Type) [Field F] [Algebra κ F]
    (θ : F ≃+* ↥(ModularCurve.x1FunctionFieldC κ M))
    (hθ : ∀ a : κ, θ (algebraMap κ F a) = algebraMap κ ↥(ModularCurve.x1FunctionFieldC κ M) a)
    (J : F) (hJ : ((θ J : ↥(ModularCurve.x1FunctionFieldC κ M)) : LaurentSeries κ) = ModularCurve.jqModC κ)
    (G : Type) [Group G] [Finite G] [MulSemiringAction G F] [FaithfulSMul G F]
    (hGκ : ∀ (g : G) (a : κ), g • algebraMap κ F a = algebraMap κ F a) (hGJ : ∀ g : G, g • J = J)
    (P : ValuationSubring F) (hPκ : ∀ a : κ, algebraMap κ F a ∈ P) (hPtop : P ≠ ⊤)
    (hPpir : IsPrincipalIdealRing ↥P) (hJP : J ∈ P) :
    Nat.card {g : G // g • P = P ∧ ∀ e : ↥P, g • (e : F) - e ∈ P.nonunits} ≤ 3 := by sorry
