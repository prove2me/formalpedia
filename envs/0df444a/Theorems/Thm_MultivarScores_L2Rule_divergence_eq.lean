-- Prove2me | Theorems.Thm_MultivarScores_L2Rule_divergence_eq
-- name    : MultivarScores.L2Rule.divergence_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T06:30:29.611882+00:00
-- url     : https://prove2.me/theorems/c8bf4958-ae19-4e3e-b424-051d57f00eed
-- title:
--   Proof of Theorem 1, p. 32 — Δ = 𝔼_{P_Y}S(P_X, •) − 𝔼_{P_Y}S(P_Y, •) = ∫ (f_X ∗ w − f_Y ∗ w)² h dz ≥ 0
-- statement:
--   Let $w$, $h$ and a class $\mathcal V^d$ of probability distributions on $\mathbb R^d$ satisfy Assumption 1, and let $P_X,P_Y\in\mathcal V^d$. Then the divergence of the L² scoring rule (2) is
--
--   $$\Delta:=\mathbb E_{P_Y}\big[S(P_X,\bullet;w,h)\big]-\mathbb E_{P_Y}\big[S(P_Y,\bullet;w,h)\big]=\int_{\mathbb R^d}\big((f_X*w)(z)-(f_Y*w)(z)\big)^2h(z)\,dz,$$
--
--   and this quantity is nonnegative.
--
--   This is the computation in the proof of Theorem 1; it shows that the divergence of $S$ is precisely the weighted L² distance (1) between the smoothed densities, from which properness follows.
--
--   **Formalization Note** $\mathbb E_{P_Y}[S(P,\bullet)]$ is the integral of $y\mapsto S(P,y;w,h)$ against $P_Y$. Assumption 1 is the structure described in the `Setting` item.
-- source:
--   Meng, Taylor, Ben Taieb, Li, Scores for Multivariate Distributions and Level Sets, arXiv:2002.09578v6, p. 32, proof of Theorem 1, divergence display

import Mathlib
import Definitions.Def_MultivarScores_L2Rule_Setting

namespace MultivarScores.L2Rule

open MeasureTheory

/-- Divergence display in the proof of Theorem 1, p. 32: under Assumption 1,
`Δ = 𝔼_{P_Y}[S(P_X, •)] − 𝔼_{P_Y}[S(P_Y, •)] = ∫ (f_X ∗ w − f_Y ∗ w)²(z) h(z) dz ≥ 0`. -/
theorem divergence_eq {d : ℕ} (w h : E d → ℝ) (𝒱 : Set (Measure (E d)))
    (hA : Assumption1 w h 𝒱) (PX PY : Measure (E d)) (hPX : PX ∈ 𝒱) (hPY : PY ∈ 𝒱) :
    (∫ y, S PX w h y ∂PY) - (∫ y, S PY w h y ∂PY) = L2div PX PY w h ∧
      0 ≤ L2div PX PY w h := by sorry

end MultivarScores.L2Rule
