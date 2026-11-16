-- Prove2me | Theorems.Thm_IAFTRL_proposition_D_2_ftrl
-- name    : IAFTRL.proposition_D_2_ftrl
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-15T08:25:07.848315+00:00
-- url     : https://prove2.me/theorems/67abb905-048b-4ed4-9ed5-c91c0c9ca5eb
-- title:
--   Proposition D.2 (FTRL bound) — $\mathrm{Reg}_T(u)\le 16d\log(eK)+21\sqrt{dT\log(eK)}$
-- statement:
--   Let $d\ge1$ and let $\mathcal A=\{a_1,\dots,a_K\}$ be a finite action set in the Euclidean unit ball of $\mathbb R^d$ that spans $\mathbb R^d$. Consider any execution of IA-FTRL for $T\ge1$ rounds against an adaptive environment whose loss vectors satisfy $\|\theta_t\|_{\mathcal A}=\max_{a\in\mathcal A}|a^\top\theta_t|\le1$, and write $\mathrm{Reg}_T(u)=\mathbb E\big[\sum_{t=1}^T(A_t-u)^\top\theta_t\big]$ for the regret against a comparator $u\in\mathcal A$. Then for every $u\in\mathcal A$,
--   $$
--   \mathrm{Reg}_T(u)\le 16\,d\log(eK)+21\sqrt{dT\log(eK)} .
--   $$
--
--   This is the substantive term of the all-history adversarial guarantee in Proposition D.2. It holds on every history, with no moment event or objective comparison, and it yields the minimax-order bound (2.4) of Proposition 2.1.
--
--   **Formalization Note** Same hypotheses as `IAFTRL.proposition_D_2`. Together with `IAFTRL.proposition_D_2_trivial` it gives that proposition.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299, Proposition D.2, p.67 (second term of the minimum)

import Mathlib
import Definitions.Def_IAFTRL_IsActionSet
import Definitions.Def_IAFTRL_IsIAFTRLRun
import Definitions.Def_IAFTRL_regretVs

namespace IAFTRL

open Matrix MeasureTheory

/-- **Proposition D.2, FTRL bound.** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits*,
arXiv:2611.01299, Proposition D.2, p.67: "IA-FTRL satisfies, for every `T ≥ 1`,
`sup_{u∈𝒜} Reg_T(u) ≤ min{2T, 16d log(eK) + 21√(dT log(eK))}`. No moment event or objective
comparison is required for this bound." — the second term of the minimum.

For every execution of IA-FTRL for `T ≥ 1` rounds against an adaptive environment (spanning finite
action set in the unit ball of `ℝ^d`, `d ≥ 1`) and every comparator action `u`:
`Reg_T(u) ≤ 16d log(eK) + 21√(dT log(eK))`.

**Formalization Note.** Same hypotheses as `IAFTRL.proposition_D_2`; together with
`IAFTRL.proposition_D_2_trivial` it gives that proposition. -/
theorem proposition_D_2_ftrl {d K : ℕ} (hd : 1 ≤ d) (arms : Fin K → Fin d → ℝ)
    (hA : IsActionSet arms) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (T : ℕ) (hT : 1 ≤ T) (R : Run d K Ω) (hR : IsIAFTRLRun P arms T R)
    (u : Fin K) :
    regretVs P arms T R u ≤
      16 * (d : ℝ) * Real.log (Real.exp 1 * K) +
        21 * Real.sqrt ((d : ℝ) * T * Real.log (Real.exp 1 * K)) := by sorry

end IAFTRL
