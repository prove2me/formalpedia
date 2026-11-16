-- Prove2me | Theorems.Thm_IAFTRL_proposition_D_2_trivial
-- name    : IAFTRL.proposition_D_2_trivial
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-15T08:25:47.770579+00:00
-- url     : https://prove2.me/theorems/2d7c31dd-3a05-4b43-8a88-d29e532d95ea
-- title:
--   Proposition D.2 (first bound) — $\mathrm{Reg}_T(u)\le 2T$
-- statement:
--   Let $d\ge1$ and let $\mathcal A=\{a_1,\dots,a_K\}$ be a finite action set in the Euclidean unit ball of $\mathbb R^d$ that spans $\mathbb R^d$. Consider any execution of IA-FTRL for $T\ge1$ rounds against an adaptive environment whose loss vectors satisfy $\|\theta_t\|_{\mathcal A}=\max_{a\in\mathcal A}|a^\top\theta_t|\le1$, and write $\mathrm{Reg}_T(u)=\mathbb E\big[\sum_{t=1}^T(A_t-u)^\top\theta_t\big]$ for the regret against a comparator $u\in\mathcal A$. Then for every $u\in\mathcal A$,
--   $$
--   \mathrm{Reg}_T(u)\le 2T .
--   $$
--
--   This is the first term of the minimum in Proposition D.2: since every per-round loss lies in $[-1,1]$, the regret never exceeds twice the horizon.
--
--   **Formalization Note** Same hypotheses as `IAFTRL.proposition_D_2`. Together with `IAFTRL.proposition_D_2_ftrl` it gives that proposition.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299, Proposition D.2, p.67 (first term of the minimum)

import Mathlib
import Definitions.Def_IAFTRL_IsActionSet
import Definitions.Def_IAFTRL_IsIAFTRLRun
import Definitions.Def_IAFTRL_regretVs

namespace IAFTRL

open Matrix MeasureTheory

/-- **Proposition D.2, first bound (`Reg_T ≤ 2T`).** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear
Bandits*, arXiv:2611.01299, Proposition D.2, p.67: "IA-FTRL satisfies, for every `T ≥ 1`,
`sup_{u∈𝒜} Reg_T(u) ≤ min{2T, 16d log(eK) + 21√(dT log(eK))}`" — the first term of the minimum.

For every execution of IA-FTRL for `T ≥ 1` rounds against an adaptive environment (spanning finite
action set in the unit ball of `ℝ^d`, `d ≥ 1`) and every comparator action `u`: `Reg_T(u) ≤ 2T`.

**Formalization Note.** Same hypotheses as `IAFTRL.proposition_D_2`; together with
`IAFTRL.proposition_D_2_ftrl` it gives that proposition. -/
theorem proposition_D_2_trivial {d K : ℕ} (hd : 1 ≤ d) (arms : Fin K → Fin d → ℝ)
    (hA : IsActionSet arms) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (T : ℕ) (hT : 1 ≤ T) (R : Run d K Ω) (hR : IsIAFTRLRun P arms T R)
    (u : Fin K) :
    regretVs P arms T R u ≤ 2 * (T : ℝ) := by sorry

end IAFTRL
