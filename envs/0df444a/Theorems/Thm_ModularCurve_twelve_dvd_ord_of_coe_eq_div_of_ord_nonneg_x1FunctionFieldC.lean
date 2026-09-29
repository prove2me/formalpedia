-- Prove2me | Theorems.Thm_ModularCurve_twelve_dvd_ord_of_coe_eq_div_of_ord_nonneg_x1FunctionFieldC
-- name    : ModularCurve.twelve_dvd_ord_of_coe_eq_div_of_ord_nonneg_x1FunctionFieldC
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/f29f5c4d-d72a-5d0b-bb95-86a6db0b2f16
-- title:
--   Divisibility by 12 of ordₓ(̄ f¹²/Δ̄) at affine places
-- statement:
--   Let $p$ be a prime and $\kappa$ an algebraically closed field of characteristic $p$, and let $M$ be a nonzero natural number with $5 \le M$ and $p \nmid M$. Let $w$ be an integral weight-one form of level $M$ over $\kappa$, i.e. a modular form of weight $1$ for $\Gamma_1(M)$ together with a power series $w.\mathrm{series}$ over $\mathbb{Z}$ whose image in $\mathbb{C}[[q]]$ is the $q$-expansion of that form and whose reduction $\mathtt{intSeriesC}\,\kappa\,w.\mathrm{series}$, the associated Laurent series over $\kappa$, is nonzero. Work inside $K_0 = \mathtt{x1FunctionFieldC}\,\kappa\,M$, the subfield of the Laurent series field $\kappa((q))$ obtained by adjoining to $\kappa$ the ratios of $q$-expansions of integral forms for $\Gamma_1(M)$. Let $J \in K_0$ have Laurent expansion $\mathtt{jqModC}\,\kappa = q^{-1}\cdot \overline{E_4^3 \Delta^{-1}q}$, the reduction to $\kappa$ of the $j$-numerator series, and let $T \in K_0$ have Laurent expansion the quotient of the reduction of $w.\mathrm{series}^{12}$ by the reduction of $q\prod_{n\ge 1}(1-q^n)^{24}$, i.e. $\bar f^{12}/\bar\Delta$. Let $x$ be a place of $K_0$ over $\kappa$ (a proper valuation subring of $K_0$ containing $\kappa$ whose ring structure is a principal ideal ring), and suppose $\operatorname{ord}_x J \ge 0$, where $\operatorname{ord}_x$ is minus the logarithm of the associated adic valuation. Then $12$ divides $\operatorname{ord}_x T$.
--
--   Inside the function field of $X_1(M)_\kappa$ this is the statement that the Hodge bundle $\omega$ is a line bundle on the fine modular curve and that $\bar\Delta$ trivialises $\omega^{\otimes 12}$ over the affine locus $\operatorname{ord}_x J \ge 0$, so that the order of $\bar f^{12}/\bar\Delta$ at such a place is $12$ times the order of $\bar f$. It is used in the analysis of the Hasse invariant root function and of ramification in the Igusa covering of $X_1(M)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_twelve_dvd_ord_of_coe_eq_div_of_ord_nonneg_x1FunctionFieldC.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X0
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve AlgebraicCurve

theorem ModularCurve.twelve_dvd_ord_of_coe_eq_div_of_ord_nonneg_x1FunctionFieldC
    (p : ℕ) [Fact p.Prime] (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ]
    (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (w : ModularCurve.IntegralWeightOneForm κ M)
    (J : ↥(ModularCurve.x1FunctionFieldC κ M)) (hJ : (J : LaurentSeries κ) = ModularCurve.jqModC κ)
    (T : ↥(ModularCurve.x1FunctionFieldC κ M))
    (hT : (T : LaurentSeries κ) =
      intSeriesC κ (w.series ^ 12) / intSeriesC κ (PowerSeries.X * ModularCurve.dedekindEtaUnit))
    (x : Place κ ↥(ModularCurve.x1FunctionFieldC κ M)) (hx : 0 ≤ x.ord J) :
    (12 : ℤ) ∣ x.ord T := by sorry
