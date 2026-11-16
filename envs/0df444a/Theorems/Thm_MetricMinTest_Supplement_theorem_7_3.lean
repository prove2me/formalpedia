-- Prove2me | Theorems.Thm_MetricMinTest_Supplement_theorem_7_3
-- name    : MetricMinTest.Supplement.theorem_7_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:44:16.406352+00:00
-- url     : https://prove2.me/theorems/d88ce696-0a4b-46bd-8294-71bc22452266
-- title:
--   Theorem 7.3, p.16 — mixed-workload upper bound: $H\le J\le\min\{F,\inf H_{Z,r}(1+\ln\rho_{Z,r})\}$, $C^\star\le1100JL$, $B^\star\le8500JL$
-- statement:
--   For every finite metric or pseudometric and $\gamma,\delta\in(0,1/4]$,
--   $$H_d(\gamma)\le J_d(\gamma)\le\min\Big\{F_d(\gamma),\ \inf_{(Z,r):\,S(Z,r)=[k]}H_{Z,r}(1+\ln\rho_{Z,r})\Big\},\tag{7.2}$$
--   $$C^\star_d(\gamma,\delta)\le1100\,J_d(\gamma)\ln(1/\delta),\qquad B^\star_d(\gamma,\delta)\le8500\,J_d(\gamma)\ln(1/\delta).\tag{7.3}$$
--   The budgeted tester stops on every input. The same upper bounds hold with the cost of any feasible regional cover in place of $J_d(\gamma)$.
--
--   Fractional composition of screening regions under one global stopping rule therefore gives an adaptive upper bound that is never worse than ball certificates or any single whole-space screening cover.
--
--   **Formalization Note** The infimum in (7.2) ranges over nonempty $Z$ and all real $r\in[0,\gamma)$ with $S(Z,r)=[k]$.
--
--   Differences from the source:
--   - encoding: a finite metric or pseudometric on $[k]$ → a pseudometric on a finite nonempty index type ($k=|\iota|\ge1$); reason: a metric is a pseudometric; $[k]$ has $k\ge1$ points
--   - encoding: admissible regions $(Z,r)$, $r<\gamma$ an occurring distance → regions indexed by $(Z,(i_0,j_0))$ with radius $d(i_0,j_0)$; reason: every occurring distance is available; duplicated regions have equal cost, so $J$ is unchanged
--   - generalization: any feasible regional cover (over the admissible regions) → any feasible regional cover in the duplicated-region indexing; reason: a cover over distinct regions is the special case supported on one index per region
--   - reading: the budgeted tester stops on every input → existence of a $(\gamma,\delta)$-valid tester with stopping time at most $8500J\ln(1/\delta)$ (resp. $8500\cdot$cost$\cdot\ln(1/\delta)$) for every private draw and every observation table; reason: a uniform budget is what makes the tester stop on every input
--   - encoding: the cost measures and testers of §2 (sequential testers with private randomness; $C^\star$, $B^\star$, $C^{\mathrm{na}}$, $B^{\mathrm{na}}$) → the published tester model (stack-of-streams observations, validity including measurability of the acceptance event and the stopping time) and $[0,\infty]$-valued infima, suprema and expectations; reason: same quantities; probabilities and expectations require measurability, and the values can be infinite
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Theorem 7.3, p.16

import Mathlib
import Definitions.Def_MetricMinTest_IsPseudometric
import Definitions.Def_MetricMinTest_infoWorkload
import Definitions.Def_MetricMinTest_certWorkload
import Definitions.Def_MetricMinTest_Bstar
import Definitions.Def_MetricMinTest_Supplement_Cstar
import Definitions.Def_MetricMinTest_Supplement_mixedWorkload
import Definitions.Def_MetricMinTest_Supplement_singleCoverInf

namespace MetricMinTest.Supplement

/-- **Theorem 7.3 (Mixed-workload upper bound).** Chen–Fang, *Minimum-Mean Testing under Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), Theorem 7.3, p.16: "For every finite metric
or pseudometric and γ, δ ∈ (0, 1/4],
H_d(γ) ≤ J_d(γ) ≤ min{F_d(γ), inf_{(Z,r): S(Z,r)=[k]} H_{Z,r}(1 + ln ρ_{Z,r})}, (7.2)
C⋆_d(γ, δ) ≤ 1100 J_d(γ) ln(1/δ), B⋆_d(γ, δ) ≤ 8500 J_d(γ) ln(1/δ). (7.3) The budgeted tester
stops on every input. The same upper bounds hold with the cost of any feasible regional cover in
place of J_d(γ)."

**Formalization Note.** `J = mixedWorkload` (program (7.1): admissible radii are the occurring
distances below `γ`); the infimum in (7.2) is `singleCoverInf d γ 1` (all real `r ∈ [0, γ)`).
"The budgeted tester stops on every input" is stated as the existence of a `(γ, δ)`-valid tester
whose stopping time is at most `8500 J ln(1/δ)` for every private draw `ξ` and every observation
table `ω`. The last sentence repeats the three upper-bound conclusions for the cost
`regionalCoverCost d γ y` of every feasible regional cover `y`. -/
theorem theorem_7_3 {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι] (d : ι → ι → ℝ)
    (hd : IsPseudometric d) (γ δ : ℝ) (hγ : γ ∈ Set.Ioc (0 : ℝ) (1 / 4))
    (hδ : δ ∈ Set.Ioc (0 : ℝ) (1 / 4)) :
    infoWorkload d γ ≤ mixedWorkload d γ ∧
    mixedWorkload d γ ≤ min (certWorkload d γ) (singleCoverInf d γ 1) ∧
    Cstar d γ δ ≤ ENNReal.ofReal (1100 * mixedWorkload d γ * Real.log (1 / δ)) ∧
    Bstar d γ δ ≤ ENNReal.ofReal (8500 * mixedWorkload d γ * Real.log (1 / δ)) ∧
    (∃ T : Tester ι, T.IsValid d γ δ ∧ ∀ ξ ω,
      ((T.stopTime ξ ω : ℕ∞) : ENNReal) ≤
        ENNReal.ofReal (8500 * mixedWorkload d γ * Real.log (1 / δ))) ∧
    ∀ y, IsRegionalCover d γ y →
      Cstar d γ δ ≤ ENNReal.ofReal (1100 * regionalCoverCost d γ y * Real.log (1 / δ)) ∧
      Bstar d γ δ ≤ ENNReal.ofReal (8500 * regionalCoverCost d γ y * Real.log (1 / δ)) ∧
      (∃ T : Tester ι, T.IsValid d γ δ ∧ ∀ ξ ω,
        ((T.stopTime ξ ω : ℕ∞) : ENNReal) ≤
          ENNReal.ofReal (8500 * regionalCoverCost d γ y * Real.log (1 / δ))) := by sorry

end MetricMinTest.Supplement
