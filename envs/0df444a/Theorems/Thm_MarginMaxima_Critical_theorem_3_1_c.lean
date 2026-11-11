-- Prove2me | Theorems.Thm_MarginMaxima_Critical_theorem_3_1_c
-- name    : MarginMaxima.Critical.theorem_3_1_c
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:03:04.452495+00:00
-- url     : https://prove2.me/theorems/ace802ea-31a2-40cd-92f9-b4680cdda810
-- title:
--   Theorem 3.1(c), (c′) — at the critical margins: $\mathrm{fat}_{\gamma_c}(F_{\max,r})\ge c\,r\ln r/\ln\ln r$ and $\mathrm{fat}^0_{1/7}(F_{\max,r})\ge c\,r\ln r/\ln\ln r$
-- statement:
--   There are absolute constants $c>0$ and $r_0$ such that for every $r\ge r_0$
--   $$\mathrm{fat}_{\gamma_c}(F_{\max,r})\ge\frac{c\,r\ln r}{\ln\ln r}\qquad\text{and}\qquad\mathrm{fat}^0_{1/7}(F_{\max,r})\ge\frac{c\,r\ln r}{\ln\ln r},$$
--   where $\gamma_c=1/(3\sqrt3)$ and both fats are suprema over all dimensions. This item is parts (c) and (c′) of Theorem 3.1; its other parts are not part of this mission. It is the case $\Delta=0$ of the lower bound in Theorem 1.1(a).
--
--   Differences from the source:
--   - encoding: fat(F_max,r) = sup_d fat(F^(d)_max,r), an integer or ∞ → fatMax / fat0Max : ℕ∞ = ⨆_{d ≥ 1} of the ℕ∞-valued fat (BartlettNN.Margin.fat, fat0); real bounds compared in ℝ≥0∞ through ENNReal.ofReal; reason: an infinite fat stays ⊤, so no upper bound is vacuous; ofReal of the positive real bounds is exact
--   - encoding: r, the number of heads → r : ℕ with 1 ≤ r; reason: the paper's r is a positive integer (§1: exactly r heads)
--   - reading: Theorem 3.1's 'absolute c > 0, r0' for its parts → one pair (c, r0) for both (c) and (c′), quantified before r; reason: the theorem fixes one c and r0 for all its parts
-- source:
--   Tianlang Chen, The Margin Complexity of Maxima of Linear Functionals, STOC 2027 submission (manuscript sha256 dbfb896a…3901), p. 6, Theorem 3.1(c), (c′)

import Mathlib
import Definitions.Def_BartlettNN_Margin_FatShattering
import Definitions.Def_MarginMaxima_Critical_MaxClass

open scoped ENNReal

namespace MarginMaxima.Critical

theorem theorem_3_1_c :
    ∃ c : ℝ, 0 < c ∧ ∃ r0 : ℕ, ∀ r : ℕ, 1 ≤ r → r0 ≤ r →
      ENNReal.ofReal (c * r * Real.log r / Real.log (Real.log r)) ≤ (fatMax r gammaC : ℝ≥0∞) ∧
      ENNReal.ofReal (c * r * Real.log r / Real.log (Real.log r)) ≤
        (fat0Max r (1 / 7) : ℝ≥0∞) := by sorry

end MarginMaxima.Critical
