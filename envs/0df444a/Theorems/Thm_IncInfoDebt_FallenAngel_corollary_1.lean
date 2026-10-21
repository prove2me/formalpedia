-- Prove2me | Theorems.Thm_IncInfoDebt_FallenAngel_corollary_1
-- name    : IncInfoDebt.FallenAngel.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:18:45.835769+00:00
-- url     : https://prove2.me/theorems/ae458d02-5566-4aba-a724-b4e12cc8ef0d
-- title:
--   Corollary 1 — Regime 4 default intensity and closed form (32)
-- statement:
--   In Regime 4, let $\sigma>0$ be volatility, $L>0$ the information lag, $m\in\mathbb R$ drift, and $a=y_{t-L}>0$ the observed lagged log distance to default. Let $p_4(y\mid a)$ be the conditional density in Lemma 1 and $H_h(a)$ the short-horizon default-probability quotient in (D.19). Define
--
--   $$\Lambda(a)=\frac{a}{\sqrt{2\pi\sigma^2L^3}}\frac{\exp[-(a+mL)^2/(2\sigma^2L)]}{N((a+mL)/\sqrt{\sigma^2L})-e^{-2am/\sigma^2}N((-a+mL)/\sqrt{\sigma^2L})}.$$
--
--   Corollary 1 states both equalities of (32):
--
--   $$\lim_{h\downarrow0}H_h(a)=\frac{\sigma^2}{2}\partial_y^+p_4(0\mid a)=\Lambda(a).$$
--
--   The formula gives the creditors' instantaneous default rate after debt capacity is exhausted, from the last observed log distance and the model parameters.
--
--   **Formalization Note** The paper multiplies (32) by $\mathbf1_{\{a>0\}}$. The theorem states the branch $a>0$, since the conditional density is undefined for a non-surviving lagged state. The derivative is from the right and the horizon limit is taken through $h>0$.
-- source:
--   Benzoni, Garlappi & Goldstein, Asymmetric Information, Dynamic Debt Issuance, and the Term Structure of Credit Spreads, Federal Reserve Bank of Chicago WP 2019-08 (20 Sept 2019; published as Incomplete Information, Debt Issuance, and the Term Structure of Credit Spreads, Management Science 2023, doi:10.1287/mnsc.2022.4529), p. 16, Corollary 1, (32), https://doi.org/10.21033/wp-2019-08

import Mathlib
import Definitions.Def_IncInfoDebt_FallenAngel_Model

namespace IncInfoDebt.FallenAngel
open Filter

/-- Corollary 1, p. 16: both equalities of the Regime 4 default-intensity formula (32). -/
theorem corollary_1 (σ m L a : ℝ) (hP : Standing σ L) (ha : 0 < a) :
    let Λ := a / Real.sqrt (2 * Real.pi * σ ^ 2 * L ^ 3) *
      (Real.exp (-(1 / (2 * σ ^ 2 * L)) * (a + m * L) ^ 2) /
        (N ((a + m * L) / Real.sqrt (σ ^ 2 * L)) -
          Real.exp (-(2 * a * m / σ ^ 2)) *
            N ((-a + m * L) / Real.sqrt (σ ^ 2 * L))))
    Tendsto (hazardQuotient σ m L a)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds Λ) ∧
    HasDerivWithinAt (condDensity σ m L a) (2 / σ ^ 2 * Λ) (Set.Ici 0) 0 := by sorry

end IncInfoDebt.FallenAngel
