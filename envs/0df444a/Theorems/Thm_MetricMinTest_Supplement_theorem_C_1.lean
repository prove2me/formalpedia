-- Prove2me | Theorems.Thm_MetricMinTest_Supplement_theorem_C_1
-- name    : MetricMinTest.Supplement.theorem_C_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:47:32.412209+00:00
-- url     : https://prove2.me/theorems/97c26323-c773-455c-9df8-5a9b5f511c77
-- title:
--   Theorem C.1, p.23 — TwoPhase$(Z,r)$ is valid, always stops, and costs $\le H_{Z,r}(16\ln\rho_{Z,r}+15\ln(1/\delta)+1)$
-- statement:
--   For every finite metric or pseudometric $d$, all $\gamma,\delta\in(0,1/4]$, every $r\in[0,\gamma)$ and every $r$-cover $Z$, the procedure TwoPhase$(Z,r)$ (shared screening with clean-up, Appendix C) is $(\gamma,\delta)$-valid, stops on every input, and satisfies
--   $$\sup_{P\in\mathcal P_d^+(\gamma)}\mathbb E_P\,\tau\le H_{Z,r}\Big(16\ln\rho_{Z,r}+15\ln\frac1\delta+1\Big).$$
--
--   This is the algorithmic content of the upper bound of Theorem C: shared screening replaces the $\ln k$ of the nonadaptive shared tester by $\ln\rho_{Z,r}$.
--
--   **Formalization Note** The statement holds for every optimal allocation $w$ of $H_{Z,r}$ used in the screening phase and every fixed order of the survivors. The index set carries a measurable structure with measurable singletons.
--
--   Differences from the source:
--   - encoding: a finite metric or pseudometric on $[k]$ → a pseudometric on a finite nonempty index type ($k=|\iota|\ge1$); reason: a metric is a pseudometric; $[k]$ has $k\ge1$ points
--   - encoding: TwoPhase$(Z,r)$ with "$w$ optimal for $H_{Z,r}$" and "a fixed order" → the procedure for every allocation $w\ge0$ of mass $H_{Z,r}$ feasible at every $z\in Z$, and every duplicate-free enumeration of the indices; reason: the procedure is defined up to these choices and the claim is for each of them
--   - reading: stops on every input → finite stopping time for every private draw and every observation table; reason: the strongest reading of "every input"
--   - encoding: measurability of the draw law $w/W$ → a measurable structure with measurable singletons on the index type; reason: needed to define the law of the draws; no instance is excluded
--   - encoding: the cost measures and testers of §2 (sequential testers with private randomness; $C^\star$, $B^\star$, $C^{\mathrm{na}}$, $B^{\mathrm{na}}$) → the published tester model (stack-of-streams observations, validity including measurability of the acceptance event and the stopping time) and $[0,\infty]$-valued infima, suprema and expectations; reason: same quantities; probabilities and expectations require measurability, and the values can be infinite
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Theorem C.1, p.23

import Mathlib
import Definitions.Def_MetricMinTest_IsPseudometric
import Definitions.Def_MetricMinTest_IsRCover
import Definitions.Def_MetricMinTest_Tester_IsValid
import Definitions.Def_MetricMinTest_Supplement_twoPhase

namespace MetricMinTest.Supplement

open MeasureTheory

/-- **Theorem C.1 (Screening with clean-up).** Chen–Fang, *Minimum-Mean Testing under Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), Theorem C.1, p.23: "For every finite metric
or pseudometric d, all γ, δ ∈ (0, 1/4], every r ∈ [0, γ), and every r-cover Z, TwoPhase(Z, r) is
(γ, δ)-valid, stops on every input, and satisfies
sup_{P∈P_d^+(γ)} E_P τ ≤ H_{Z,r}(16 ln ρ_{Z,r} + 15 ln(1/δ) + 1)."

**Formalization Note.** `TwoPhase(Z, r)` is `twoPhase d γ δ Z r w ord`, stated for every optimal
allocation `w` of `H_{Z,r}` (nonnegative, mass `H_{Z,r}`, feasible for every `z ∈ Z`) and
every fixed order of the survivors (`ord` any duplicate-free enumeration of the indices). The
index type is finite and nonempty and carries a measurable structure with measurable singletons
(for the draw law `w/W`). Validity is the published `Tester.IsValid`; "stops on every input" is
a finite stopping time for every private draw `ξ` and every observation table `ω`; `E_P τ` is
the `ℝ≥0∞` integral of the stopping time under `μξ ⊗ streamLaw P`. -/
theorem theorem_C_1 {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (d : ι → ι → ℝ) (hd : IsPseudometric d) (γ δ : ℝ)
    (hγ : γ ∈ Set.Ioc (0 : ℝ) (1 / 4)) (hδ : δ ∈ Set.Ioc (0 : ℝ) (1 / 4)) (r : ℝ) (hr0 : 0 ≤ r)
    (hrγ : r < γ) (Z : Finset ι) (hZ : IsRCover d Z r) (w : ι → ℝ) (hw0 : ∀ j, 0 ≤ w j)
    (hwmass : ∑ j, w j = regionWorkload d γ Z r)
    (hwfeas : ∀ z ∈ Z, 1 ≤ ∑ j, w j * (max (γ - r - d z j) 0) ^ 2)
    (ord : List ι) (hnodup : ord.Nodup) (hall : ∀ z, z ∈ ord) :
    (twoPhase d γ δ Z r w ord).IsValid d γ δ ∧
    (∀ ξ ω, (twoPhase d γ δ Z r w ord).stopTime ξ ω ≠ ⊤) ∧
    (⨆ (P : Instance ι) (_ : IsPositive d γ P),
      ∫⁻ p, (((twoPhase d γ δ Z r w ord).stopTime p.1 p.2 : ℕ∞) : ENNReal)
        ∂((twoPhase d γ δ Z r w ord).μξ.prod (streamLaw P))) ≤
      ENNReal.ofReal (regionWorkload d γ Z r *
        (16 * Real.log (regionRatio d γ Z r) + 15 * Real.log (1 / δ) + 1)) := by sorry

end MetricMinTest.Supplement
