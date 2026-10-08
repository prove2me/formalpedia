-- Prove2me | Theorems.Thm_GlynnSTS_Limit_theorem_2_4
-- name    : GlynnSTS.Limit.theorem_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:16:54.863182+00:00
-- url     : https://prove2.me/theorems/3261993b-2c8b-45da-86fb-ab59ba26fe40
-- title:
--   Theorem 2.4, p. 3 — for g ∈ 𝓜, (Ȳₙ(1) − μ)/g(Ȳₙ) ⇒ B(1)/g(B) under Assumption (2.1)
-- statement:
--   Let $Y = \{Y(t) : t \ge 0\}$ be a real-valued measurable process, $\bar Y_n(t) = \frac1n\int_0^{nt}Y(s)\,ds$ for $0 \le t \le 1$, and suppose Assumption (2.1) holds: for finite constants $\mu$ and $\sigma > 0$, $X_n = n^{1/2}(\bar Y_n - \mu k) \Rightarrow \sigma B$ in $C[0,1]$, where $B$ is a standard Brownian motion and $k(t) = t$. Let $g \in \mathcal M$, i.e. $g : C[0,1] \to \mathbb R$ is measurable and (i) $g(\alpha x) = \alpha g(x)$ for $\alpha > 0$; (ii) $g(x - \beta k) = g(x)$ for $\beta \in \mathbb R$; (iii) $P\{g(B) > 0\} = 1$; (iv) $P\{B \in D(g)\} = 0$. Then
--   $$\frac{\bar Y_n(1) - \mu}{g(\bar Y_n)} \Rightarrow \frac{B(1)}{g(B)}\qquad (n \to \infty).$$
--
--   This is display (2.5), the basic limit theorem of the method of standardized time series. The unknown variance constant $\sigma$ does not appear in the limit, so quantiles of $B(1)/g(B)$ give asymptotic confidence intervals for the steady-state mean $\mu$ without estimating $\sigma$.
--
--   **Formalization Note** Convergence in distribution is Mathlib's `TendstoInDistribution`. Division by zero returns $0$ in Lean; this affects only the event $\{g(\bar Y_n) = 0\}$ and, in the limit, the null event $\{g(B) = 0\}$, and matches the paper's convention for $h$ in the proof.
-- source:
--   Glynn & Iglehart, Simulation output analysis using standardized time series, Math. Oper. Res. 15 (1990), p. 3, Theorem 2.4, display (2.5)

import Mathlib
import Definitions.Def_GlynnSTS_Limit_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace GlynnSTS.Limit

theorem theorem_2_4 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Ω → C(unitInterval, ℝ)) (hB : IsStdBMC P B)
    (Y : ℝ → Ω → ℝ) (Ybar : ℕ → Ω → C(unitInterval, ℝ)) (μ σ : ℝ)
    (h21 : Assumption21 P Y Ybar μ σ B)
    (g : C(unitInterval, ℝ) → ℝ) (hg : ClassM P B g) :
    TendstoInDistribution (fun (n : ℕ) ω => (Ybar n ω 1 - μ) / g (Ybar n ω)) atTop
      (fun ω => B ω 1 / g (B ω)) (fun _ => P) P := by sorry

end GlynnSTS.Limit
