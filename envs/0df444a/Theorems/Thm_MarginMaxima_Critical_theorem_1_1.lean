-- Prove2me | Theorems.Thm_MarginMaxima_Critical_theorem_1_1
-- name    : MarginMaxima.Critical.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:03:32.99298+00:00
-- url     : https://prove2.me/theorems/b30de83c-67dd-4e60-8b1d-1ab0ae387747
-- title:
--   Theorem 1.1 — critical margins $1/(3\sqrt3)$ and $1/7$: $c\,r\ln r/(\gamma^2L)\le\mathrm{fat}(F_{\max,r})\le C\,r\ln r/\gamma^2$ below them, $\le 12.5r/(\gamma-\gamma_{cr})^2$ above
-- statement:
--   There are absolute constants $C,c>0$ and $r_0$ such that the following hold, with $\gamma_{cr}=\gamma_c=1/(3\sqrt3)$ and $\mathrm{fat}=\mathrm{fat}_\gamma$, and also with $\gamma_{cr}=1/7$ and $\mathrm{fat}=\mathrm{fat}^0_\gamma$.
--
--   (a) Let $0<\gamma\le\gamma_{cr}$, $\Delta=\gamma_{cr}-\gamma$ and $L=\min\{\ln(e/\Delta),\ln\ln r\}$, with $\ln(e/0)=\infty$. For all $r\ge r_0$,
--   $$\frac{c\,r\ln r}{\gamma^2L}\le\mathrm{fat}(F_{\max,r})\le\frac{C\,r\ln r}{\gamma^2}.$$
--   (b) For $\gamma>\gamma_{cr}$ and all $r$: $\mathrm{fat}(F_{\max,r})\le 12.5\,r/(\gamma-\gamma_{cr})^2$.
--
--   Here $F_{\max,r}$ is the class of maxima of $r$ linear functionals of norm at most $1$ on the unit ball, and fat is the supremum over all dimensions. The theorem locates the two critical margins at which the fat-shattering dimension changes from $\Theta(r\ln r)$ to $O(r)$ growth.
--
--   Differences from the source:
--   - encoding: fat(F_max,r) = sup_d fat(F^(d)_max,r), an integer or ∞ → fatMax / fat0Max : ℕ∞ = ⨆_{d ≥ 1} of the ℕ∞-valued fat (BartlettNN.Margin.fat, fat0); real bounds compared in ℝ≥0∞ through ENNReal.ofReal; reason: an infinite fat stays ⊤, so no upper bound is vacuous; ofReal of the positive real bounds is exact
--   - encoding: L = min{ln(e/∆), ln ln r} with ln(e/0) = ∞ → Lfactor (γcr − γ) r = if ∆ = 0 then log (log r) else min (log (exp 1/∆)) (log (log r)); reason: Lean's log (e/0) = log 0 = 0 would make L = 0
--   - encoding: r, the number of heads → r : ℕ with 1 ≤ r; reason: the paper's r is a positive integer (§1: exactly r heads)
--   - encoding: x ↦ max_{j≤r}⟨u_j, x⟩ on the unit ball of R^d, ∥u_j∥ ≤ 1, labels in {±1} → MaxClass d r: functions on the closed-ball subtype Ball d, ⨆ over j : Fin r of inner ℝ (u j) x, ‖u j‖ ≤ 1; labels Bool read through pm; reason: for r ≥ 1 the supremum over Fin r is the maximum of r reals; pm true = 1, pm false = −1
-- source:
--   Tianlang Chen, The Margin Complexity of Maxima of Linear Functionals, STOC 2027 submission (manuscript sha256 dbfb896a…3901), p. 2, Theorem 1.1

import Mathlib
import Definitions.Def_BartlettNN_Margin_FatShattering
import Definitions.Def_MarginMaxima_Critical_MaxClass

open BartlettNN.Margin
open scoped ENNReal

namespace MarginMaxima.Critical

theorem theorem_1_1 :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ r0 : ℕ,
      ((∀ γ : ℝ, 0 < γ → γ ≤ gammaC → ∀ r : ℕ, 1 ≤ r → r0 ≤ r →
          ENNReal.ofReal (c * r * Real.log r / (γ ^ 2 * Lfactor (gammaC - γ) r))
              ≤ (fatMax r γ : ℝ≥0∞) ∧
            (fatMax r γ : ℝ≥0∞) ≤ ENNReal.ofReal (C * r * Real.log r / γ ^ 2)) ∧
        (∀ γ : ℝ, gammaC < γ → ∀ r : ℕ, 1 ≤ r →
          (fatMax r γ : ℝ≥0∞) ≤ ENNReal.ofReal (12.5 * r / (γ - gammaC) ^ 2))) ∧
      ((∀ γ : ℝ, 0 < γ → γ ≤ 1 / 7 → ∀ r : ℕ, 1 ≤ r → r0 ≤ r →
          ENNReal.ofReal (c * r * Real.log r / (γ ^ 2 * Lfactor (1 / 7 - γ) r))
              ≤ (fat0Max r γ : ℝ≥0∞) ∧
            (fat0Max r γ : ℝ≥0∞) ≤ ENNReal.ofReal (C * r * Real.log r / γ ^ 2)) ∧
        (∀ γ : ℝ, 1 / 7 < γ → ∀ r : ℕ, 1 ≤ r →
          (fat0Max r γ : ℝ≥0∞) ≤ ENNReal.ofReal (12.5 * r / (γ - 1 / 7) ^ 2))) := by sorry

end MarginMaxima.Critical
