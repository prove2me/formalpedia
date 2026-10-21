-- Prove2me | Theorems.Thm_JSEQDelay_Diffusion_proposition_A_2_osc
-- name    : JSEQDelay.Diffusion.proposition_A_2_osc
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:18:24.805674+00:00
-- url     : https://prove2.me/theorems/16332a78-9156-438d-be4d-052625dec375
-- title:
--   Proposition A.2, property 1, p. 36 — oscillation inequality (74) for the Skorokhod map
-- statement:
--   Let $x$ be right-continuous with left limits on $[0,\infty)$ with $x(0)\ge0$, and let $0\le s<t<\infty$. With $\mathrm{Osc}(f,[s,t])=\sup\{|f(u)-f(r)|:r,u\in[s,t]\}$,
--   $$\mathrm{Osc}(\Gamma_1(x),[s,t])\le\mathrm{Osc}(x,[s,t])\quad\text{and}\quad\mathrm{Osc}(\Gamma_2(x),[s,t])\le\mathrm{Osc}(x,[s,t]).$$
--
--   The inequality turns moduli of continuity of the net input into moduli of continuity of queue length and idleness; it is the tool behind the C-tightness of Lemma 5.2.
--
--   **Formalization Note** The page writes the index set as "$s\le r,u\le t$", meaning $r,u\in[s,t]$. Oscillations are computed in $[0,\infty]$.
-- source:
--   Atar & Lipshutz, Heavy traffic limits for join the shortest estimated queue policy using delayed information, authors' manuscript of January 12, 2020 (Math. Oper. Res. 46(3), 2021, doi:10.1287/moor.2020.1056), p. 36, Appendix A, Proposition A.2, property 1, (74)

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_RankBasedSDI_LoadBalancing_Reflection
import Definitions.Def_JSEQDelay_Diffusion_Skorokhod

namespace JSEQDelay.Diffusion

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open BellWilliams2001.ThresholdPolicy RankBasedSDI.LoadBalancing

/-- **Proposition A.2, property 1** (oscillation inequality (74), p. 36): for
`x ∈ 𝔻₊([0, ∞), ℝ)` and `0 ≤ s < t < ∞`,
`Osc(Γ₁(x), [s, t]) ≤ Osc(x, [s, t])` and `Osc(Γ₂(x), [s, t]) ≤ Osc(x, [s, t])`, where
`Osc(f, [s, t]) = sup{|f(u) − f(r)| : r, u ∈ [s, t]}`. -/
theorem proposition_A_2_osc (x : ℝ → ℝ) (hx : IsCadlag x) (hx0 : 0 ≤ x 0)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s < t) :
    osc (Gamma1 x) s t ≤ osc x s t ∧ osc (skorokhodReg x) s t ≤ osc x s t := by sorry

end JSEQDelay.Diffusion
