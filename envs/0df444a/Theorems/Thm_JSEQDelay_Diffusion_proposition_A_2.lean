-- Prove2me | Theorems.Thm_JSEQDelay_Diffusion_proposition_A_2
-- name    : JSEQDelay.Diffusion.proposition_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:17:53.322245+00:00
-- url     : https://prove2.me/theorems/2af66150-daf8-4aab-8bff-ab1ee2300a9e
-- title:
--   Proposition A.2, p. 36 — the one-dimensional Skorokhod problem has the unique solution (Γ₁, Γ₂)(x)
-- statement:
--   Let $x$ be right-continuous with left limits on $[0,\infty)$ and $x(0)\ge0$. Then the one-dimensional Skorokhod problem for $x$ has a unique solution, namely $(z,y)=(\Gamma_1(x),\Gamma_2(x))$, where for $t\ge0$
--   $$\Gamma_1(x)(t)=x(t)+\Gamma_2(x)(t),\qquad \Gamma_2(x)(t)=\sup_{0\le s\le t}(x(s))^-.$$
--
--   This classical fact identifies the scaled queue length and idleness of each server (Remark 2.1) and is used throughout the proofs.
--
--   **Formalization Note** Uniqueness is stated on $[0,\infty)$. The case $x(0)=0$ is posed separately on the platform as `BellWilliams2001.ThresholdPolicy.skorokhod_problem_1d` (open), in the form $-\inf x$; this item has $x(0)\ge0$ and the form (73).
-- source:
--   Atar & Lipshutz, Heavy traffic limits for join the shortest estimated queue policy using delayed information, authors' manuscript of January 12, 2020 (Math. Oper. Res. 46(3), 2021, doi:10.1287/moor.2020.1056), p. 36, Appendix A, Proposition A.2 (main clause), (72)–(73)

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_RankBasedSDI_LoadBalancing_Reflection
import Definitions.Def_JSEQDelay_Diffusion_Skorokhod

namespace JSEQDelay.Diffusion

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open BellWilliams2001.ThresholdPolicy RankBasedSDI.LoadBalancing

/-- **Proposition A.2**, main clause (p. 36): for `x ∈ 𝔻₊([0, ∞), ℝ)` (RCLL with `x(0) ≥ 0`),
`(Γ₁(x), Γ₂(x))` solves the one-dimensional Skorokhod problem for `x`, where
`Γ₂(x)(t) = sup_{0 ≤ s ≤ t} (x(s))⁻` (73) and `Γ₁(x) = x + Γ₂(x)` (72), and every solution
`(z, y)` equals `(Γ₁(x), Γ₂(x))` on `[0, ∞)`. -/
theorem proposition_A_2 (x : ℝ → ℝ) (hx : IsCadlag x) (hx0 : 0 ≤ x 0) :
    SkorokhodSolves x (Gamma1 x) (skorokhodReg x) ∧
    ∀ z y : ℝ → ℝ, SkorokhodSolves x z y →
      ∀ t, 0 ≤ t → z t = Gamma1 x t ∧ y t = skorokhodReg x t := by sorry

end JSEQDelay.Diffusion
