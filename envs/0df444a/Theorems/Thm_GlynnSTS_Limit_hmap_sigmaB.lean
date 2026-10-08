-- Prove2me | Theorems.Thm_GlynnSTS_Limit_hmap_sigmaB
-- name    : GlynnSTS.Limit.hmap_sigmaB
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:16:34.614087+00:00
-- url     : https://prove2.me/theorems/32b7a36c-5350-4110-a9cf-7e8530974952
-- title:
--   Proof of Theorem 2.4, p. 3 — by (2.3i), h(σB) = B(1)/g(B)
-- statement:
--   Let $g : C[0,1] \to \mathbb R$ satisfy (2.3i), $g(\alpha x) = \alpha g(x)$ for all $\alpha > 0$ and $x \in C[0,1]$, and let $h(x) = x(1)/g(x)$ for $g(x) \ne 0$, $h(x) = 0$ otherwise. For every $\sigma > 0$ and every path $B(\omega)$,
--   $$h(\sigma B) = \frac{B(1)}{g(B)}.$$
--
--   This identifies the limit in the continuous-mapping step of the proof of Theorem 2.4: the scale $\sigma$ cancels.
--
--   **Formalization Note** Only (2.3i) is assumed, which makes the statement stronger than its use in the paper. The identity holds for every $\omega$; where $g(B(\omega)) = 0$, both sides are $0$ (the right-hand side because Lean's division by zero returns $0$).
-- source:
--   Glynn & Iglehart, Simulation output analysis using standardized time series, Math. Oper. Res. 15 (1990), p. 3, proof of Theorem 2.4

import Mathlib
import Definitions.Def_GlynnSTS_Limit_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace GlynnSTS.Limit

theorem hmap_sigmaB {Ω : Type*} (B : Ω → C(unitInterval, ℝ)) (g : C(unitInterval, ℝ) → ℝ)
    (hhom : ∀ a : ℝ, 0 < a → ∀ x, g (a • x) = a * g x) (σ : ℝ) (hσ : 0 < σ) :
    ∀ ω, hmap g (σ • B ω) = B ω 1 / g (B ω) := by sorry

end GlynnSTS.Limit
