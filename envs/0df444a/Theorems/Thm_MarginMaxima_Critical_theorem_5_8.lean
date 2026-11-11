-- Prove2me | Theorems.Thm_MarginMaxima_Critical_theorem_5_8
-- name    : MarginMaxima.Critical.theorem_5_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:02:56.044097+00:00
-- url     : https://prove2.me/theorems/aaff9438-93cd-43c9-a749-57747c088dec
-- title:
--   Theorem 5.8 — onset: for $\Delta\in(0,\gamma_{cr})$ and $\ln r\ge C_0\Delta^{-2}\ln^2(e/\Delta)$, $\mathrm{fat}_{\gamma_{cr}-\Delta}\ge c_1 r\ln r/\ln(e/\Delta)$
-- statement:
--   There are absolute constants $c_1,C_0$ such that, with $\gamma_{cr}=\gamma_c$ and $\mathrm{fat}=\mathrm{fat}_\gamma$, and with $\gamma_{cr}=1/7$ and $\mathrm{fat}=\mathrm{fat}^0_\gamma$: for $\Delta\in(0,\gamma_{cr})$ and $\ln r\ge C_0\Delta^{-2}\ln^2(e/\Delta)$,
--   $$\mathrm{fat}_{\gamma_{cr}-\Delta}(F_{\max,r})\ge\frac{c_1\,r\ln r}{\ln(e/\Delta)}.$$
--
--   Differences from the source:
--   - reading: absolute c₁, C₀ in a lower bound → ∃ c₁ C₀ : ℝ with 0 < c₁, quantified before both instances, Δ and r; reason: a lower bound with c₁ ≤ 0 is empty; one pair serves both instances as printed
--   - encoding: fat(F_max,r) = sup_d fat(F^(d)_max,r), an integer or ∞ → fatMax / fat0Max : ℕ∞ = ⨆_{d ≥ 1} of the ℕ∞-valued fat (BartlettNN.Margin.fat, fat0); real bounds compared in ℝ≥0∞ through ENNReal.ofReal; reason: an infinite fat stays ⊤, so no upper bound is vacuous; ofReal of the positive real bounds is exact
--   - encoding: r, the number of heads → r : ℕ with 1 ≤ r; reason: the paper's r is a positive integer (§1: exactly r heads)
-- source:
--   Tianlang Chen, The Margin Complexity of Maxima of Linear Functionals, STOC 2027 submission (manuscript sha256 dbfb896a…3901), p. 12, Theorem 5.8

import Mathlib
import Definitions.Def_BartlettNN_Margin_FatShattering
import Definitions.Def_MarginMaxima_Critical_MaxClass

open scoped ENNReal

namespace MarginMaxima.Critical

theorem theorem_5_8 :
    ∃ c1 C0 : ℝ, 0 < c1 ∧
      (∀ Δ : ℝ, 0 < Δ → Δ < gammaC → ∀ r : ℕ, 1 ≤ r →
        C0 * Δ ^ (-2 : ℤ) * Real.log (Real.exp 1 / Δ) ^ 2 ≤ Real.log r →
        ENNReal.ofReal (c1 * r * Real.log r / Real.log (Real.exp 1 / Δ)) ≤
          (fatMax r (gammaC - Δ) : ℝ≥0∞)) ∧
      (∀ Δ : ℝ, 0 < Δ → Δ < 1 / 7 → ∀ r : ℕ, 1 ≤ r →
        C0 * Δ ^ (-2 : ℤ) * Real.log (Real.exp 1 / Δ) ^ 2 ≤ Real.log r →
        ENNReal.ofReal (c1 * r * Real.log r / Real.log (Real.exp 1 / Δ)) ≤
          (fat0Max r (1 / 7 - Δ) : ℝ≥0∞)) := by sorry

end MarginMaxima.Critical
