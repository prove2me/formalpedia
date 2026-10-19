-- Prove2me | Theorems.Thm_LogMeanVar_Complete_c2_spike_le
-- name    : LogMeanVar.Complete.c2_spike_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:10:34.382651+00:00
-- url     : https://prove2.me/theorems/95ff4777-b20a-40bc-b723-fd13866bf216
-- title:
--   Proof of Theorem 2 (App. C.2), p. O–11 — J(t, R_t; π^{h,v}) ≤ J(t, R_t; π̂) for every h > 0 and v ∈ ℝ
-- statement:
--   In the complete market with $\sigma>0$, $\gamma>0$, $T>0$ and a real Brownian motion $B$, let $\hat\pi\equiv(\mu-r)/((1+\gamma)\sigma^2)$ be the constant strategy. For every $t\in[0,T)$, every starting log-wealth $y$, every $v\in\mathbb R$ and every $h>0$,
--   $$J(t,y;\pi^{h,v})\ \le\ J(t,y;\hat\pi),$$
--   where $\pi^{h,v}$ holds $v$ on $[t,t+h)$ and $\hat\pi$ afterwards.
--
--   No perturbation, however long, improves the reward of $\hat\pi$; this is stronger than the first-order condition of Definition 1 and implies it.
--
--   **Formalization Note** The page's "$J(,R_t,X_t;\hat\pi)$" lacks its argument $t$. The inequality is stated for every $h>0$, including $h\ge T-t$ (perturbation on the whole remaining horizon). The coordinates of $B$ are assumed measurable.
-- source:
--   Dai, Jin, Kou, Xu, A Dynamic Mean-Variance Analysis for Log Returns, SSRN 3437268 (version of Aug 2019), p. O-11, Proof of Theorem 2 (App. C.2), last paragraph

import Mathlib
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Definitions.Def_LogMeanVar_Complete_Market
import Definitions.Def_LogMeanVar_Complete_LogReturn
import Definitions.Def_LogMeanVar_Complete_Equilibrium

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace LogMeanVar.Complete

/-- Dai, Jin, Kou, Xu, A Dynamic Mean-Variance Analysis for Log Returns, SSRN 3437268 (version of Aug 2019), p. O–11, Proof of Theorem 2 (App. C.2), last paragraph, second clause: for the
constant strategy `π̂ ≡ (μ - r)/((1 + γ)σ²)`, every `t ∈ [0, T)`, every starting log-wealth
`y`, every `v ∈ ℝ` and every `h > 0`, `J(t, y; π^{h,v}) ≤ J(t, y; π̂)`.

**Formalization Note** The printed "J(,R_t,X_t; π̂)" lacks its first argument `t`. The
inequality is stated for every `h > 0`, which is how the proof uses it; it is stronger than the
`liminf` of Definition 1. -/
theorem c2_spike_le (M : Market) (hM : M.Standing) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (hBm : ∀ s, Measurable (B s))
    (t : ℝ) (ht : t ∈ Ico 0 M.T) (y v h : ℝ) (hh : 0 < h) :
    J M P B (spike (fun _ _ => piHat M) t h v) t y ≤ J M P B (fun _ _ => piHat M) t y := by sorry

end LogMeanVar.Complete
