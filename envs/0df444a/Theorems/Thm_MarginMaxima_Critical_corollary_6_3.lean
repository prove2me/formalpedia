-- Prove2me | Theorems.Thm_MarginMaxima_Critical_corollary_6_3
-- name    : MarginMaxima.Critical.corollary_6_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:03:17.565056+00:00
-- url     : https://prove2.me/theorems/6fe346ef-1708-43ed-be15-54ac1c5596e4
-- title:
--   Corollary 6.3 — small margins: $\sup_d\mathrm{fat}^0_\gamma\ge c'R^2r\ln r/\gamma^2$ for $0<\gamma\le g_\star R$, and $\Theta(R^2r\ln r/\gamma^2)$ for $R$-bounded linear or affine maxima
-- statement:
--   There are absolute $c',r_0$ such that for $r\ge r_0$, $R>0$ and $0<\gamma\le g_\star R$: the $r$-fold maximum of linear functions of norm at most $R$ on the unit ball satisfies
--   $$\sup_d\mathrm{fat}^0_\gamma\ge c'R^2r\ln r/\gamma^2,$$
--   and the bound holds in all sufficiently large finite dimensions. Together with Theorem 3 of [AK24], the fat-shattering dimension of $r$-fold maxima of $R$-bounded linear or affine functions is $\Theta(R^2r\ln r/\gamma^2)$ in this range of $\gamma$.
--
--   Differences from the source:
--   - reading: the bound holds in all sufficiently large finite dimensions → ∃ D₀, ∀ d ≥ D₀, c′R²r ln r/γ² ≤ fat⁰_γ(F^(d)_max,r(R)); reason: literal
--   - reading: Together with Theorem 3 of [AK24], fat of r-fold maxima of R-bounded linear or affine functions is Θ(R²r ln r/γ²) → an absolute C′ > 0 and, for the same r, R, γ, c′R²r ln r/γ² ≤ sup_d fat_γ ≤ C′R²r ln r/γ² for MaxClassR and for AffMaxClassR (‖u‖ ≤ R, |b| ≤ R); reason: Θ with absolute constants; c′ serves the lower half since fat⁰ ≤ fat and linear ⊆ affine; [AK24] is not assumed (Theorem C.1 supplies the upper half)
--   - encoding: fat(F_max,r) = sup_d fat(F^(d)_max,r), an integer or ∞ → fatMax / fat0Max : ℕ∞ = ⨆_{d ≥ 1} of the ℕ∞-valued fat (BartlettNN.Margin.fat, fat0); real bounds compared in ℝ≥0∞ through ENNReal.ofReal; reason: an infinite fat stays ⊤, so no upper bound is vacuous; ofReal of the positive real bounds is exact
--   - encoding: r, the number of heads → r : ℕ with 1 ≤ r; reason: the paper's r is a positive integer (§1: exactly r heads)
-- source:
--   Tianlang Chen, The Margin Complexity of Maxima of Linear Functionals, STOC 2027 submission (manuscript sha256 dbfb896a…3901), p. 13, Corollary 6.3

import Mathlib
import Definitions.Def_BartlettNN_Margin_FatShattering
import Definitions.Def_MarginMaxima_Critical_MaxClass

open BartlettNN.Margin
open scoped ENNReal

namespace MarginMaxima.Critical

theorem corollary_6_3 :
    ∃ c' C' : ℝ, 0 < c' ∧ 0 < C' ∧ ∃ r0 : ℕ, ∀ r : ℕ, 1 ≤ r → r0 ≤ r →
      ∀ R γ : ℝ, 0 < R → 0 < γ → γ ≤ gStar * R →
        ENNReal.ofReal (c' * R ^ 2 * r * Real.log r / γ ^ 2) ≤
            ((⨆ (d : ℕ) (_ : 1 ≤ d), fat0 (MaxClassR d r R) γ : ℕ∞) : ℝ≥0∞) ∧
          (∃ D0 : ℕ, ∀ d : ℕ, D0 ≤ d →
            ENNReal.ofReal (c' * R ^ 2 * r * Real.log r / γ ^ 2) ≤
              (fat0 (MaxClassR d r R) γ : ℝ≥0∞)) ∧
          ENNReal.ofReal (c' * R ^ 2 * r * Real.log r / γ ^ 2) ≤
            ((⨆ (d : ℕ) (_ : 1 ≤ d), fat (MaxClassR d r R) γ : ℕ∞) : ℝ≥0∞) ∧
          ((⨆ (d : ℕ) (_ : 1 ≤ d), fat (MaxClassR d r R) γ : ℕ∞) : ℝ≥0∞) ≤
            ENNReal.ofReal (C' * R ^ 2 * r * Real.log r / γ ^ 2) ∧
          ENNReal.ofReal (c' * R ^ 2 * r * Real.log r / γ ^ 2) ≤
            ((⨆ (d : ℕ) (_ : 1 ≤ d), fat (AffMaxClassR d r R) γ : ℕ∞) : ℝ≥0∞) ∧
          ((⨆ (d : ℕ) (_ : 1 ≤ d), fat (AffMaxClassR d r R) γ : ℕ∞) : ℝ≥0∞) ≤
            ENNReal.ofReal (C' * R ^ 2 * r * Real.log r / γ ^ 2) := by sorry

end MarginMaxima.Critical
