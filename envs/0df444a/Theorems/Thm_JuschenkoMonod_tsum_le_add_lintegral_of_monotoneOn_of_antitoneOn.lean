-- Prove2me | Theorems.Thm_JuschenkoMonod_tsum_le_add_lintegral_of_monotoneOn_of_antitoneOn
-- name    : JuschenkoMonod.tsum_le_add_lintegral_of_monotoneOn_of_antitoneOn
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T17:22:08.080511+00:00
-- url     : https://prove2.me/theorems/d0de881e-ebe1-4a71-8f44-8d402f67d228
-- title:
--   Lemma 2.5 — ∑_{j≥0} φ(j) ≤ φ(t₀) + ∫₀^∞ φ for φ increasing on [0, t₀] and decreasing on [t₀, ∞)
-- statement:
--   Let $t_0 \ge 0$, and let $\varphi$ be a function from $\mathbf R$ to $[0, \infty)$ that is nondecreasing on $[0, t_0]$ and nonincreasing on $[t_0, \infty)$. Then $$\sum_{j \ge 0}\varphi(j) \le \varphi(t_0) + \int_0^\infty \varphi(t)\,dt,$$ where both sides are computed in $[0, \infty]$.
--
--   *Formalization note.* The function is defined on $\mathbf R$ rather than on $\mathbf R_{\ge0}$; only its values on $[0, \infty)$ enter. "Increasing" and "decreasing" are read in the weak sense. Sums and integrals are taken in $[0, \infty]$, so the inequality also covers the case of a divergent integral.
-- source:
--   Juschenko, K. and Monod, N., Cantor systems, piecewise translations and simple amenable groups, Ann. of Math. (2) 178 (2013) 775–787, https://doi.org/10.4007/annals.2013.178.2.7, p. 779, Lemma 2.5

import Mathlib

open MeasureTheory
open scoped ENNReal NNReal

namespace JuschenkoMonod

theorem tsum_le_add_lintegral_of_monotoneOn_of_antitoneOn (t₀ : ℝ) (ht₀ : 0 ≤ t₀) (φ : ℝ → ℝ≥0)
    (hinc : MonotoneOn φ (Set.Icc 0 t₀)) (hdec : AntitoneOn φ (Set.Ici t₀)) :
    ∑' j : ℕ, (φ j : ℝ≥0∞) ≤ φ t₀ + ∫⁻ t in Set.Ici 0, φ t := by
  sorry

end JuschenkoMonod
