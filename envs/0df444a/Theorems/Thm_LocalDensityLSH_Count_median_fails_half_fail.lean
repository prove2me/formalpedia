-- Prove2me | Theorems.Thm_LocalDensityLSH_Count_median_fails_half_fail
-- name    : LocalDensityLSH.Count.median_fails_half_fail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:22:43.653804+00:00
-- url     : https://prove2.me/theorems/d4b2be52-5c6f-4df8-a063-c378c85a3db3
-- title:
--   §5, pp. 15–16, median of means — if the median of E_1, …, E_M fails, at least M/2 of the E_m fail
-- statement:
--   Let $E_1,\dots,E_M$ be real numbers, $c$ a target value and $r$ a tolerance. Say that $E_m$ *fails* if $|E_m-c|>r$. If the median $\operatorname{med}(E_1,\dots,E_M)$ fails, i.e. $|\operatorname{med}-c|>r$, then
--   $$\#\{m : |E_m-c|>r\}\ \ge\ \frac M2 .$$
--
--   Consequently $\mathbb P(\text{median of }E_m\text{ fails})\le\mathbb P(\text{half of }E_m\text{ fail})=\mathbb P(F\ge M/2)$ for $F=\sum_m F_m$, the number of failing estimates: this is the deterministic half of the median-of-means argument.
--
--   **Formalization Note.** The median is the lower median (entry $\lfloor (M-1)/2\rfloor$ of the sorted list); the statement holds for any order statistic between the two middle ones, and trivially for $M=0$.
-- source:
--   Wu, Charikar & Natchu, Local Density Estimation in High Dimensions, arXiv:1809.07471v1, §5, pp. 15–16 (median of means paragraph)

import Mathlib
import Definitions.Def_LocalDensityLSH_Count_Model
import Definitions.Def_LocalDensityLSH_Count_Estimator

namespace LocalDensityLSH.Count

open MeasureTheory ProbabilityTheory

/-- §5, pp. 15–16: if the median of the estimates `e₁, …, e_M` is farther than `r` from `c`, then
at least `M/2` of the estimates are farther than `r` from `c` ("the median fails only if half of
the `E_m` fail"). -/
theorem median_fails_half_fail {M : ℕ} (e : Fin M → ℝ) (c r : ℝ)
    (h : r < |median e - c|) :
    (M : ℝ) / 2 ≤ ((Finset.univ.filter (fun m => r < |e m - c|)).card : ℝ) := by sorry

end LocalDensityLSH.Count
