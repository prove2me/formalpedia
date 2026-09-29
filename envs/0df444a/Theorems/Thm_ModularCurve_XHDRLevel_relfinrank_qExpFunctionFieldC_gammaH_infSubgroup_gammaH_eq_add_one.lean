-- Prove2me | Theorems.Thm_ModularCurve_XHDRLevel_relfinrank_qExpFunctionFieldC_gammaH_infSubgroup_gammaH_eq_add_one
-- name    : ModularCurve.XHDRLevel.relfinrank_qExpFunctionFieldC_gammaH_infSubgroup_gammaH_eq_add_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/4e6a3b7f-5560-5366-a843-eb14577195fe
-- title:
--   Degree p+1 of X_H(M) over X_{H'}(M/p)
-- statement:
--   Let $p$ be a prime and $M$ a nonzero natural number, let $H$ be a subgroup of $(\mathbb{Z}/M)^\times$, and assume $p \mid M$ but $p^2 \nmid M$, and that every unit $u$ of $\mathbb{Z}/M$ whose image under the reduction map $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ is trivial lies in $H$. For a subgroup $\Gamma \le \mathrm{SL}_2(\mathbb{Z})$, write $F(\Gamma) =$ `qExpFunctionFieldC ℚ Γ` for the intermediate field of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the ratios $f/g$ of Laurent series coming from integral $q$-expansions (power series over $\mathbb{Z}$, base changed to $\mathbb{Q}$) of pairs of modular forms $f,g$ of one and the same weight on the image of $\Gamma$ in $\mathrm{GL}_2(\mathbb{R})$, with the series attached to $g$ nonzero; and for a modulus $N$ and a subgroup $H' \le (\mathbb{Z}/N)^\times$ let $\Gamma_{H'}(N) \le \mathrm{SL}_2(\mathbb{Z})$ be the group of matrices in $\Gamma_0(N)$ whose lower right entry, reduced mod $N$, lies in $H'$. Let $H'$ be the image of $H$ in $(\mathbb{Z}/(M/p))^\times$. Then the relative degree (`IntermediateField.relfinrank`) of $F(\Gamma_{H'}(M/p))$ inside $F(\Gamma_H(M))$, both read as subfields of $\mathbb{Q}((q))$, equals $p+1$; since the first is contained in the second, this is the degree $[F(\Gamma_H(M)) : F(\Gamma_{H'}(M/p))]$.
--
--   This is the degree computation for the forgetful map $X_H(M) \to X_{H'}(M/p)$ when $p$ exactly divides $M$ and $H$ contains the kernel of reduction, so that $\Gamma_H(M) = \Gamma_{H'}(M/p) \cap \Gamma_0(p)$ has index $p+1$; it is expressed purely in terms of $q$-expansion function fields, with the relative degree taken inside $\mathbb{Q}((q))$ so that no intermediate algebra structure has to be named. It is used in the analysis of the valuation subrings of $F(\Gamma_H(M))$ above the generic point of the $j$-line in characteristic $p$ (the Gauss valuation and its Atkin–Lehner translate) and in the construction of the model of $X_H(M)$ at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRLevel_relfinrank_qExpFunctionFieldC_gammaH_infSubgroup_gammaH_eq_add_one.lean

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

theorem ModularCurve.XHDRLevel.relfinrank_qExpFunctionFieldC_gammaH_infSubgroup_gammaH_eq_add_one
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) :
    IntermediateField.relfinrank (qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))
      (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) = p + 1 := by sorry
