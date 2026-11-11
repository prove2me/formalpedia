-- Prove2me | Theorems.Thm_HighMagSampling_SK_fact_1
-- name    : HighMagSampling.SK.fact_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:28:37.132369+00:00
-- url     : https://prove2.me/theorems/f1a990de-9cad-4a0b-bff8-7c6d786904b9
-- title:
--   Fact 1 — for $J\sim\mathrm{GOE}(d)$: $\max|J_{ij}|\le C\sqrt{\log(d/\delta)/d}$ and $\|J\|_{\mathrm{op}}\le 2+C\sqrt{\log(1/\delta)/d}$ w.p. $\ge1-\delta$
-- statement:
--   Let $J\sim\mathrm{GOE}(d)$ (Model 1): $J$ is symmetric, its entries $J_{ij}$, $i<j$, are i.i.d. $N(0,\tfrac1d)$, its diagonal entries are i.i.d. $N(0,\tfrac2d)$, all independent. There is a constant $C>0$ such that for every $d\ge1$ and every $\delta\in(0,\tfrac12)$, with probability at least $1-\delta$, simultaneously
--   $$\max_{i,j}|J_{ij}|\le C\sqrt{\frac{\log(d/\delta)}{d}}\qquad\text{and}\qquad\|J\|_{\mathrm{op}}\le 2+C\sqrt{\frac{\log(1/\delta)}{d}} .$$
--
--   These are the standard entrywise and spectral-norm bounds for the GOE (Vershynin §2.5; Anderson–Guionnet–Zeitouni Thm 2.3.5) that the paper uses for the SK model.
--
--   **Formalization Note.** Model 1 is the published `RandMatDisc.goe d`, a law on `Fin d → Fin d → ℝ`; a sample is read as `Matrix.of J`. "With probability at least $1-\delta$" is stated as: the set of $J$ where the conclusion fails has measure at most $\delta$ (no measurability of the event is presupposed).
--
--   Differences from the source:
--   - encoding: "with probability $\ge1-\delta$" → the failure set has $\mathrm{GOE}(d)$-measure $\le\delta$; reason: equivalent for a measurable event, and does not presuppose measurability.
--   - reading: "for an appropriate constant $C>0$" → one $C$ chosen before $d$ and $\delta$; reason: the constant is universal (it is quantified before "for any $\delta$" and depends on nothing).
--   - encoding: $\max_{i,j}|J_{ij}|\le B$ → $|J_{ij}|\le B$ for all $i,j$; reason: equivalent.
-- source:
--   Kumar, Sarkar, Tian, Zhu, High-Magnetization Sampling at Low Temperatures, arXiv:2609.08873v1, p. 12, Fact 1 (with Model 1, p. 12)

import Mathlib
import Definitions.Def_RandMatDisc_goe
import Definitions.Def_HighMagSampling_SK_Spectral

open MeasureTheory

namespace HighMagSampling.SK

/-- Fact 1, p. 12: there is a constant `C > 0` such that for every `d ≥ 1` and `δ ∈ (0, 1/2)`,
with probability `≥ 1 − δ` over `J ∼ GOE(d)` (Model 1), simultaneously
`max_{i,j} |J_ij| ≤ C √(log(d/δ)/d)` and `‖J‖_op ≤ 2 + C √(log(1/δ)/d)`. Stated as: the failure
set has `GOE(d)`-measure at most `δ`. -/
theorem fact_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 1 ≤ d → ∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
      RandMatDisc.goe d {J | ¬ ((∀ i j, |J i j| ≤ C * Real.sqrt (Real.log (d / δ) / d)) ∧
          opNorm (Matrix.of J) ≤ 2 + C * Real.sqrt (Real.log (1 / δ) / d))} ≤
        ENNReal.ofReal δ := by sorry

end HighMagSampling.SK
