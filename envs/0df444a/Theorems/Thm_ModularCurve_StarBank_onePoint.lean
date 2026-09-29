-- Prove2me | Theorems.Thm_ModularCurve_StarBank_onePoint
-- name    : ModularCurve.StarBank.onePoint
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/31c10fd7-bb04-514e-81dd-cdd1e203001b
-- title:
--   One-point case: (j-β₀)Δ is a nonzero constant
-- statement:
--   Let $K$ be a field, $M$ a natural number whose image in $K$ is nonzero, and let $c, \beta_0 \in K$ with $c \neq 0$. Work in the Laurent series field $K((q))$ (Hahn series over $\mathbb{Z}$ with values in $K$), and write $j$ for [`ModularCurve.jqModC K`](def/ModularCurve_JqCoeff.html#L15), namely $q^{-1}$ times the image in $K$ of the integral power series `jNum` $=$ `eisenstein4`$^3 \cdot$ `dedekindEtaUnitInv`, and $\Delta$ for the element $q \cdot \bigl(\prod_{n \ge 1}(1 - q^{n})\bigr)^{24}$, obtained from the integral power series `etaProd` $= \prod_{n \ge 0}(1 - X^{n+1})$ by reducing its coefficients into $K$, raising to the $24$th power and multiplying by $q$. Assume that evaluating the polynomial $c\,(X - \beta_0)^M$ at $j$ and multiplying by $\Delta^M$ gives $1$, i.e. $c\,(j - \beta_0)^M \Delta^M = 1$ in $K((q))$. Then there exists $\gamma \in K$, $\gamma \neq 0$, such that $(j - \beta_0)\,\Delta$ equals the constant Laurent series $\gamma$.
--
--   This is the extraction of an $M$-th root in $K((q))$ in the degenerate case where the polynomial relation $G(j)\Delta^M = 1$ involves a single $j$-value $\beta_0$: invertibility of $M$ in $K$ forces the $M$-th root $(j-\beta_0)\Delta$ of the constant $c^{-1}$ to be itself constant. It is used by [`ModularCurve.StarBank.starBank`](thm.html#ModularCurve.StarBank.starBank) in the analysis of $q$-expansion relations on the modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_StarBank_onePoint.lean

import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial HahnSeries ModularCurve

theorem ModularCurve.StarBank.onePoint {K : Type*} [Field K] {M : ℕ}
    (hM : (M : K) ≠ 0) {c : K} (hc : c ≠ 0) {β₀ : K}
    (hstar : Polynomial.aeval (ModularCurve.jqModC K)
          (Polynomial.C c * (Polynomial.X - Polynomial.C β₀) ^ M)
        * (HahnSeries.single (1 : ℤ) 1
            * HahnSeries.ofPowerSeries ℤ K
                (PowerSeries.map (Int.castRingHom K) ModularCurve.etaProd) ^ 24) ^ M
        = 1) :
    ∃ γ : K, γ ≠ 0 ∧
      (ModularCurve.jqModC K - HahnSeries.C β₀)
        * (HahnSeries.single (1 : ℤ) 1
            * HahnSeries.ofPowerSeries ℤ K
                (PowerSeries.map (Int.castRingHom K) ModularCurve.etaProd) ^ 24)
        = HahnSeries.C γ := by sorry
