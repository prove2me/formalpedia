-- Prove2me | Theorems.Thm_GlynnSTS_Limit_hmap_Xn_tendsto
-- name    : GlynnSTS.Limit.hmap_Xn_tendsto
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:16:32.66982+00:00
-- url     : https://prove2.me/theorems/0d4dc2dc-b82b-4f98-874d-7bb672884f41
-- title:
--   Proof of Theorem 2.4, p. 3 — h(Xₙ) ⇒ h(σB) by the continuous mapping theorem
-- statement:
--   Assume (2.1): $Y$ is a measurable process, $\bar Y_n(t) = \frac1n\int_0^{nt}Y(s)\,ds$, $X_n(t) = n^{1/2}(\bar Y_n(t) - \mu t)$, and $X_n \Rightarrow \sigma B$ in $C[0,1]$ for a standard Brownian motion $B$ and constants $\mu$, $\sigma > 0$. Let $g \in \mathcal M$ and let $h(x) = x(1)/g(x)$ for $g(x) \ne 0$, $h(x) = 0$ otherwise. Then
--   $$h(X_n) \Rightarrow h(\sigma B)\qquad (n \to \infty),$$
--   convergence in distribution of real random variables.
--
--   This is the continuous-mapping step of the proof of Theorem 2.4.
-- source:
--   Glynn & Iglehart, Simulation output analysis using standardized time series, Math. Oper. Res. 15 (1990), p. 3, proof of Theorem 2.4

import Mathlib
import Definitions.Def_GlynnSTS_Limit_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace GlynnSTS.Limit

theorem hmap_Xn_tendsto {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Ω → C(unitInterval, ℝ)) (hB : IsStdBMC P B)
    (Y : ℝ → Ω → ℝ) (Ybar : ℕ → Ω → C(unitInterval, ℝ)) (μ σ : ℝ)
    (h21 : Assumption21 P Y Ybar μ σ B)
    (g : C(unitInterval, ℝ) → ℝ) (hg : ClassM P B g) :
    TendstoInDistribution (fun (n : ℕ) ω => hmap g (Xn Ybar μ n ω)) atTop
      (fun ω => hmap g (σ • B ω)) (fun _ => P) P := by sorry

end GlynnSTS.Limit
