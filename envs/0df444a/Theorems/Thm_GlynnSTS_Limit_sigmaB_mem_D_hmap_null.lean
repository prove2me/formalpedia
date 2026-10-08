-- Prove2me | Theorems.Thm_GlynnSTS_Limit_sigmaB_mem_D_hmap_null
-- name    : GlynnSTS.Limit.sigmaB_mem_D_hmap_null
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:16:10.837704+00:00
-- url     : https://prove2.me/theorems/7c5e94d3-dd17-44fa-950c-04e6759f6533
-- title:
--   Proof of Theorem 2.4, p. 3 — P{σB ∈ D(h)} = 0 for g ∈ 𝓜
-- statement:
--   Let $B$ be a standard Brownian motion in $C[0,1]$ on $(\Omega,\mathcal F,P)$, let $g \in \mathcal M$ (the class of (2.3)), and let $h(x) = x(1)/g(x)$ for $g(x) \ne 0$ and $h(x) = 0$ otherwise. For every $\sigma > 0$,
--   $$P\{\sigma B \in D(h)\} = 0,$$
--   where $D(h)$ is the set of discontinuity points of $h$.
--
--   This is the hypothesis of the continuous mapping theorem in the proof of Theorem 2.4: it shows that $h$ is almost surely continuous at the limit $\sigma B$ of Assumption (2.1).
--
--   **Formalization Note** $P$ of the set $\{\omega : \sigma B(\omega) \in D(h)\}$ is its outer measure, so no measurability of $D(h)$ is assumed.
-- source:
--   Glynn & Iglehart, Simulation output analysis using standardized time series, Math. Oper. Res. 15 (1990), p. 3, proof of Theorem 2.4

import Mathlib
import Definitions.Def_GlynnSTS_Limit_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace GlynnSTS.Limit

theorem sigmaB_mem_D_hmap_null {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B : Ω → C(unitInterval, ℝ)) (hB : IsStdBMC P B)
    (g : C(unitInterval, ℝ) → ℝ) (hg : ClassM P B g) (σ : ℝ) (hσ : 0 < σ) :
    P {ω | σ • B ω ∈ D (hmap g)} = 0 := by sorry

end GlynnSTS.Limit
