-- Prove2me | Theorems.Thm_ModularCurve_qExpFunctionFieldC_gamma0_eq_modularFunctionFieldC_of_not_dvd
-- name    : ModularCurve.qExpFunctionFieldC_gamma0_eq_modularFunctionFieldC_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/a6ff374c-085f-552d-827e-7b0f0f877677
-- title:
--   Igusa's q-expansion theorem for Γ₀(M) in characteristic p ∤ M
-- statement:
--   Let $K$ be a field, let $M$ be a nonzero natural number, let $p$ be a prime, and assume $K$ has characteristic $p$ with $p \nmid M$. Two intermediate fields of the Laurent series field $K((q))$ over $K$ are compared. The first is [`ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M)`](def/ModularCurve_X1.html#L101), the subfield generated over $K$ by the set `intFormRatiosC K (Gamma0 M)` of all quotients $\mathrm{intSeriesC}\,K\,p_f / \mathrm{intSeriesC}\,K\,p_g$, taken over integers $k$, pairs of modular forms $f, g$ of weight $k$ for the image of $\Gamma_0(M)$ in $\mathrm{GL}_2(\mathbb{R})$, and integral power series $p_f, p_g$ over $\mathbb{Z}$ satisfying `IsIntegralQExp f pf` and `IsIntegralQExp g pg`, with $\mathrm{intSeriesC}\,K\,p_g \neq 0$; here `intSeriesC` turns an integral $q$-expansion into an element of $K((q))$. The second is [`ModularCurve.modularFunctionFieldC K M`](def/ModularCurve_JqCoeff.html#L61), the subfield generated over $K$ by the two elements `jqModC K`, namely $q^{-1}$ times the image in $K[[q]]$ of the integral series `jNum` under coefficientwise reduction, and `jqNModC K M`, its image under the substitution `qExpand K M` replacing $q$ by $q^M$. The assertion is that these two intermediate fields are equal.
--
--   This is Igusa's theorem for $X_0(M)$ in characteristic $p \nmid M$, in $q$-expansion form: the field cut out at the cusp $\infty$ by reductions of integral $q$-expansions of $\Gamma_0(M)$-forms is exactly $K(j(q), j(q^M))$, so that the modular equation $\Phi_M(X, j) = 0$ remains irreducible modulo $p$. It is used in the study of the reductions of modular curves, in particular in the analysis of Igusa nodes on the full-level curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_qExpFunctionFieldC_gamma0_eq_modularFunctionFieldC_of_not_dvd.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.qExpFunctionFieldC_gamma0_eq_modularFunctionFieldC_of_not_dvd
    (K : Type*) [Field K] (M : ℕ) [NeZero M] (p : ℕ) [Fact p.Prime] [CharP K p] (hpM : ¬ p ∣ M) :
    ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M) = ModularCurve.modularFunctionFieldC K M := by sorry
