-- Prove2me | Theorems.Thm_MetricMinTest_theorem_B_2
-- name    : MetricMinTest.theorem_B_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:12:11.199331+00:00
-- url     : https://prove2.me/theorems/5a2c8a1f-f701-437b-b057-029654eb4e06
-- title:
--   Theorem B.2, p.23 — the shared allocation tester is valid, stops within $N_w$ queries, and $B^\star\le\lceil24H\ln(k/\delta)\rceil$
-- statement:
--   Let $d$ be a pseudometric on $k\ge1$ indices, $\gamma,\delta\in(0,1/4]$, and let $w\ge0$ be feasible for (1.1), with mass $W$. The shared allocation tester (draw $I_t\sim w/W$, update every target statistic, mark targets at their first crossing of $L=\ln(1/\delta)$, accept when all are marked, reject after $N_w$ queries) is $(\gamma,\delta)$-valid and stops within
--   $$N_w=\big\lceil16W\big(\ln(k/\delta)+\tfrac12\ln(1/\delta)\big)\big\rceil$$
--   queries. Consequently
--   $$B^\star_d(\gamma,\delta)\le\big\lceil24H_d(\gamma)\ln(k/\delta)\big\rceil.$$
--
--   Run for all $N_w$ queries, this tester is nonadaptive; it supplies the nonadaptive upper bound of Theorem 4.9.
--
--   Differences from the source:
--   - encoding: $k$ indices → a finite nonempty index type; reason: the paper's $k$ is a positive integer
--   - encoding: "stops within $N_w$ queries", and "every input and realization" in $B^\star$ → for every private draw and every observation table; reason: every realization
--   - encoding: testers and validity → the stack-of-streams Lean model, the index type carrying measurable singletons for the draw law; reason: Lean model of §2
--   - encoding: the minimum $H_d(\gamma)$ of (1.1) → the real infimum of the feasible masses; reason: the feasible set is nonempty and bounded below and the minimum is attained (p.7), so the value is the same
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Theorem B.2, p.23

import Mathlib
import Definitions.Def_MetricMinTest_IsPseudometric
import Definitions.Def_MetricMinTest_sharedTester
import Definitions.Def_MetricMinTest_Tester_IsValid
import Definitions.Def_MetricMinTest_Bstar
import Definitions.Def_MetricMinTest_infoWorkload

namespace MetricMinTest

/-- **Theorem B.2 (Shared allocation tester).** Chen–Fang, *Minimum-Mean Testing under Metric
Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), Theorem B.2, p.23: for a
feasible `w` in (1.1) with mass `W`, "The tester is valid and stops within N_w queries. Thus
B⋆_d(γ, δ) ≤ ⌈24H ln(k/δ)⌉", with `N_w = ⌈16W(ln(k/δ) + ½ ln(1/δ))⌉`.

**Formalization Note.** Standing setting (§2, p.6): `d` a pseudometric on `k = |ι| ≥ 1` indices,
`γ, δ ∈ (0, 1/4]`. The tester is `sharedTester` (draws `ξ ∼ (w/W)^⊗ℕ`; the index type carries a
measurable structure with measurable singletons). "Stops within N_w queries" holds for every draw
and every observation table. -/
theorem theorem_B_2 {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (d : ι → ι → ℝ) (hd : IsPseudometric d) (γ δ : ℝ)
    (hγ : γ ∈ Set.Ioc (0 : ℝ) (1 / 4)) (hδ : δ ∈ Set.Ioc (0 : ℝ) (1 / 4)) (w : ι → ℝ)
    (hw0 : ∀ j, 0 ≤ w j) (hw : ∀ i, 1 ≤ ∑ j, w j * (max (γ - d i j) 0) ^ 2) :
    (sharedTester d γ δ w).IsValid d γ δ ∧
    (∀ ξ ω, (sharedTester d γ δ w).stopTime ξ ω ≤
      (⌈16 * (∑ j, w j) *
        (Real.log ((Fintype.card ι : ℝ) / δ) + 1 / 2 * Real.log (1 / δ))⌉₊ : ℕ∞)) ∧
    Bstar d γ δ ≤
      ((⌈24 * infoWorkload d γ * Real.log ((Fintype.card ι : ℝ) / δ)⌉₊ : ℕ) : ENNReal) := by sorry

end MetricMinTest
