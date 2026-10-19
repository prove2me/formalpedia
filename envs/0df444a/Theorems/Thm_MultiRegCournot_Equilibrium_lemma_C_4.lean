-- Prove2me | Theorems.Thm_MultiRegCournot_Equilibrium_lemma_C_4
-- name    : MultiRegCournot.Equilibrium.lemma_C_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:14:47.616145+00:00
-- url     : https://prove2.me/theorems/f5c9437e-9a2e-4143-b0c6-7e6a4dda471e
-- title:
--   Lemma C.4, p. 33 — comparative statics of Q̂
-- statement:
--   Increase firm i's marginal profit from x to y within [0,w̄], holding other firms' marginal profits fixed. (i) Total sales in each region do not increase, and fall strictly where i initially sells. (ii) Every other firm's regional and total sales do not decrease. (iii) Firm i's regional and total sales do not increase, and its total sales fall strictly when initially positive.
--
--   $$x<y\Longrightarrow\hat q_r^{tot}(y,\rho^{-i})\le\hat q_r^{tot}(x,\rho^{-i}),\quad\hat q_r^j(x,\rho^{-i})\le\hat q_r^j(y,\rho^{-i})\;(j\ne i),\quad\hat q_r^i(y,\rho^{-i})\le\hat q_r^i(x,\rho^{-i}).$$
--
--   The Lean statement also includes the printed strict clauses and both firms' total-output comparisons.
--
--   **Formalization Note** The Lean model uses firms and regions indexed from zero, firm-first allocations, a C² inverse demand on ℝ that is decreasing and concave for nonnegative quantities, nonnegative reservation prices, positive capacities, and nonnegative production and transport costs.
-- source:
--   Alsabah, Bernard, Capponi, Iyengar & Sethuraman, Multiregional oligopoly with capacity constraints, SSRN 3280688 (version of June 6, 2020), p. 33, Lemma C.4 (i)–(iii)

import Mathlib
import Definitions.Def_MultiRegCournot_Equilibrium_Model

namespace MultiRegCournot.Equilibrium

/-- Lemma C.4, p. 33: all three comparative-statics clauses. -/
theorem lemma_C_4 {N R : ℕ} (M : Market N R) (hM : M.Standing) :
    ∀ rho ∈ M.box, ∀ i, ∀ x y : ℝ,
      x ∈ Set.Icc (0 : ℝ) M.wbar → y ∈ Set.Icc (0 : ℝ) M.wbar → x < y →
      let Qx := M.Qhat (Function.update rho i x)
      let Qy := M.Qhat (Function.update rho i y)
      (∀ r, qTotRegion Qy r ≤ qTotRegion Qx r ∧
        (0 < Qx i r → qTotRegion Qy r < qTotRegion Qx r)) ∧
      (∀ j, j ≠ i →
        (∀ r, Qx j r ≤ Qy j r) ∧ qTotFirm Qx j ≤ qTotFirm Qy j) ∧
      (∀ r, Qy i r ≤ Qx i r) ∧
      qTotFirm Qy i ≤ qTotFirm Qx i ∧
      (0 < qTotFirm Qx i → qTotFirm Qy i < qTotFirm Qx i) := by sorry

end MultiRegCournot.Equilibrium
