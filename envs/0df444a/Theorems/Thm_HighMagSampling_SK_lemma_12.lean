-- Prove2me | Theorems.Thm_HighMagSampling_SK_lemma_12
-- name    : HighMagSampling.SK.lemma_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:29:17.528321+00:00
-- url     : https://prove2.me/theorems/c558e460-79af-40bc-bf6f-6fb8c4d9b532
-- title:
--   Lemma 12 — four simultaneous high-probability events for $J\sim\mathrm{GOE}(d)$
-- statement:
--   There is a universal constant $C>0$ such that for every $d\ge1$ and $\delta\in(0,\tfrac12)$, with probability at least $1-\delta$ over $J\sim\mathrm{GOE}(d)$ (Model 1), the following hold simultaneously:
--
--   1. for all $S\subseteq[d]$ with $|S|=s\in[d]$, $\|J_{S\times S}\|_{\mathrm{op}}\le C\sqrt{(s\log\frac{ed}{s}+\log\frac d\delta)/d}$;
--   2. $\max_{i,j}|J_{ij}|\le C\sqrt{\log(d/\delta)/d}$ and $\|J\mathbf 1_d\|_\infty\le C\sqrt{\log(d/\delta)}$;
--   3. for all nonzero $u\in\mathbb R^d$, with $q=\|u\|_2^2/\|u\|_1^2$, $|u^\top Ju|\le C\|u\|_1^2\big(\sqrt{q\log(edq)/d}+q\sqrt{\log(d/\delta)/d}\big)$;
--   4. with $H=J\circ J-\frac1d(\mathbf 1_d\mathbf 1_d^\top-I_d)$, $\|H\|_{\mathrm{op}}\le C\big(\sqrt{\log(d/\delta)/d}+\log(d/\delta)/d\big)$.
--
--   $$\Pr_{J\sim\mathrm{GOE}(d)}\big[\text{Items 1–4 hold}\big]\ \ge\ 1-\delta .$$
--
--   This is the single random event on which the whole analysis of Theorem 4 runs; Lemma 13 is deterministic given Items 2–4.
--
--   **Formalization Note.** The four items are the mission's predicates `event1`–`event4` applied to `Matrix.of J`; `RandMatDisc.goe d` is Model 1.
--
--   Differences from the source:
--   - encoding: "with probability $\ge1-\delta$" → the failure set has $\mathrm{GOE}(d)$-measure $\le\delta$; reason: equivalent for a measurable event, and does not presuppose measurability.
--   - reading: "$C>0$ a sufficiently large universal constant" → there is one $C>0$, chosen before $d$ and $\delta$; reason: each item only weakens as $C$ grows, so "every sufficiently large $C$" and "some $C$" are the same claim.
-- source:
--   Kumar, Sarkar, Tian, Zhu, High-Magnetization Sampling at Low Temperatures, arXiv:2609.08873v1, pp. 25–26, Lemma 12

import Mathlib
import Definitions.Def_RandMatDisc_goe
import Definitions.Def_HighMagSampling_SK_GOEEvents

open MeasureTheory

namespace HighMagSampling.SK

/-- Lemma 12, pp. 25–26: there is a universal constant `C > 0` such that for every `d ≥ 1` and
`δ ∈ (0, 1/2)` the four events of Lemma 12 hold simultaneously with probability `≥ 1 − δ` over
`J ∼ GOE(d)` (Model 1). Stated as: the failure set has `GOE(d)`-measure at most `δ`. -/
theorem lemma_12 :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 1 ≤ d → ∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
      RandMatDisc.goe d {J | ¬ (event1 C d δ (Matrix.of J) ∧ event2 C d δ (Matrix.of J) ∧
          event3 C d δ (Matrix.of J) ∧ event4 C d δ (Matrix.of J))} ≤
        ENNReal.ofReal δ := by sorry

end HighMagSampling.SK
