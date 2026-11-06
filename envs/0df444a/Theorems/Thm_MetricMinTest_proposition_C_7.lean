-- Prove2me | Theorems.Thm_MetricMinTest_proposition_C_7
-- name    : MetricMinTest.proposition_C_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:12:31.218352+00:00
-- url     : https://prove2.me/theorems/b8c83df5-a7b7-4191-ab90-95b56cef4e3f
-- title:
--   Proposition C.7, p.25 — two-round screening: validity, expected cost and budget
-- statement:
--   Let $d$ be a pseudometric on a finite index set, $\gamma,\delta\in(0,1/4]$, $r\in[0,\gamma)$, $Z$ an $r$-cover, and $w$ an optimal allocation for $H_{Z,r}$. Then TwoRound$(Z,r)$ is a $(\gamma,\delta)$-valid two-round tester with
--   $$\sup_{P\in\mathcal P_d^+(\gamma)}\mathbb E_P\tau\le H_{Z,r}\Big(60\ln\frac1\delta+16\ln\rho_{Z,r}+16\ln(1+\ln|Z|)+1\Big).$$
--   Moreover, some $(\gamma,\delta)$-valid two-round tester uses at most
--   $$\big(1216(\ln\rho_{Z,r}+\ln(1+\ln|Z|))+8450\big)H_{Z,r}\ln(1/\delta)$$
--   queries on every input and realization.
--
--   On $d_m$ with $Z$ all indices and $r=0$ this gives the two-round bounds of Theorem A.
--
--   **Formalization Note** The budget clause is stated as an upper bound on the optimal two-round budget $B^{(2)}_d(\gamma,\delta)$.
--
--   Differences from the source:
--   - encoding: "w optimal for $H_{Z,r}$" → $w\ge0$ feasible with $\sum_jw_j=H_{Z,r}$, given as an argument of TwoRound; reason: the procedure is defined from an optimal allocation (p.23)
--   - encoding: "some valid two-round tester uses at most $X$ queries on every input and realization" → $B^{(2)}_d(\gamma,\delta)\le X$ with budgets over every private draw and every table; reason: definition of the optimal budget
--   - encoding: testers → the stack-of-streams Lean model with adaptedness inside validity, the index type carrying measurable singletons; reason: Lean model of Definition C.6
--   - encoding: the minimum $H_{Z,r}$ of Definition 7.1 → the real infimum of the feasible masses; reason: the feasible set is nonempty for $r<\gamma$, $Z\ne\emptyset$ and bounded below, and $w$ optimal attains it, so the value is the same
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Proposition C.7, p.25

import Mathlib
import Definitions.Def_MetricMinTest_IsPseudometric
import Definitions.Def_MetricMinTest_IsRCover
import Definitions.Def_MetricMinTest_twoRound
import Definitions.Def_MetricMinTest_RoundTester_IsValid
import Definitions.Def_MetricMinTest_Bround
import Definitions.Def_MetricMinTest_regionWorkload
import Definitions.Def_MetricMinTest_regionRatio

namespace MetricMinTest

open MeasureTheory

/-- **Proposition C.7 (Two-round screening).** Chen–Fang, *Minimum-Mean Testing under Metric
Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), Proposition C.7, p.25:
"For every finite metric or pseudometric d, all γ, δ ∈ (0, 1/4], every r ∈ [0, γ), and every
r-cover Z, TwoRound(Z, r) is a (γ, δ)-valid two-round tester with
sup_{P ∈ P_d^+(γ)} E_P τ ≤ H_{Z,r}(60 ln(1/δ) + 16 ln ρ_{Z,r} + 16 ln(1 + ln |Z|) + 1). Moreover,
some (γ, δ)-valid two-round tester uses at most (1216(ln ρ_{Z,r} + ln(1 + ln |Z|)) + 8450)
H_{Z,r} ln(1/δ) queries on every input and realization."

**Formalization Note.** `TwoRound(Z, r)` is `twoRound d γ δ Z r w` for an allocation `w` optimal
for `H_{Z,r}` (`w ≥ 0`, feasible, mass `H_{Z,r}`), as the procedure prescribes (p.23). "Valid
two-round tester" is `RoundTester.IsValid` (which includes adaptedness). `τ` is the total number of
queries. "Uses at most X queries on every input and realization" is `B^(2) ≤ X` for the optimal
two-round budget `Bround 2`, which requires the bound for every draw and every table. The index type
carries a measurable structure with measurable singletons. -/
theorem proposition_C_7 {ι : Type} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (d : ι → ι → ℝ) (hd : IsPseudometric d) (γ δ : ℝ)
    (hγ : γ ∈ Set.Ioc (0 : ℝ) (1 / 4)) (hδ : δ ∈ Set.Ioc (0 : ℝ) (1 / 4)) (r : ℝ)
    (hr : r ∈ Set.Ico 0 γ) (Z : Finset ι) (hZ : IsRCover d Z r) (w : ι → ℝ)
    (hw0 : ∀ j, 0 ≤ w j) (hwZ : ∀ z ∈ Z, 1 ≤ ∑ j, w j * (max (γ - r - d z j) 0) ^ 2)
    (hwopt : ∑ j, w j = regionWorkload d γ Z r) :
    (twoRound d γ δ Z r w).IsValid d γ δ ∧
    (⨆ (P : Instance ι) (_ : IsPositive d γ P),
        ∫⁻ p, ((twoRound d γ δ Z r w).cost p.1 p.2 : ENNReal)
          ∂((twoRound d γ δ Z r w).μξ.prod (streamLaw P))) ≤
      ENNReal.ofReal (regionWorkload d γ Z r * (60 * Real.log (1 / δ) +
        16 * Real.log (regionRatio d γ Z r) + 16 * Real.log (1 + Real.log (Z.card : ℝ)) + 1)) ∧
    Bround 2 d γ δ ≤
      ENNReal.ofReal ((1216 * (Real.log (regionRatio d γ Z r) +
        Real.log (1 + Real.log (Z.card : ℝ))) + 8450) * regionWorkload d γ Z r *
          Real.log (1 / δ)) := by sorry

end MetricMinTest
