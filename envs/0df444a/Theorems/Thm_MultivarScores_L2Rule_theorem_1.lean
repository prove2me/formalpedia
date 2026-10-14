-- Prove2me | Theorems.Thm_MultivarScores_L2Rule_theorem_1
-- name    : MultivarScores.L2Rule.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:30:39.492998+00:00
-- url     : https://prove2.me/theorems/1218aad5-c617-44f7-ab48-6366e4f0c6ae
-- title:
--   Theorem 1, p. 8 — the L² scoring rules (2) and (3) are proper, strictly proper under characterization, with divergence (1)
-- statement:
--   Let $w$ be a kernel, $h$ a weight and $\mathcal V^d$ a class of probability distributions on $\mathbb R^d$ satisfying Assumption 1. Write $\mathbb E_{P_Y}[S(P_X,\bullet)]=\int S(P_X,y;w,h)\,dP_Y(y)$ and likewise for $S'$. Then:
--
--   1. **Divergence.** For all $P_X,P_Y\in\mathcal V^d$, both L² scoring rules (2) and (3) have the divergence (1):
--   $$\mathbb E_{P_Y}[S(P_X,\bullet)]-\mathbb E_{P_Y}[S(P_Y,\bullet)]=\mathbb E_{P_Y}[S'(P_X,\bullet)]-\mathbb E_{P_Y}[S'(P_Y,\bullet)]=\int_{\mathbb R^d}\big((f_X*w)(z)-(f_Y*w)(z)\big)^2h(z)\,dz.$$
--   2. **Properness.** For all $P_X,P_Y\in\mathcal V^d$, $\mathbb E_{P_Y}[S(P_Y,\bullet)]\le\mathbb E_{P_Y}[S(P_X,\bullet)]$ and $\mathbb E_{P_Y}[S'(P_Y,\bullet)]\le\mathbb E_{P_Y}[S'(P_X,\bullet)]$.
--   3. **Strict properness.** If moreover $h$ is nonzero $\mathcal L^d$-a.e. and $f_Y*w$ uniquely characterizes every $P_Y\in\mathcal V^d$ (that is, $f_X*w=f_Y*w$ a.e. implies $P_X=P_Y$ within $\mathcal V^d$), then for all $P_X\ne P_Y$ in $\mathcal V^d$ both inequalities are strict.
--
--   The theorem generalizes the quadratic score's divergence to the weighted L² distance between smoothed densities; with the Heaviside kernel it yields the multivariate CRPS, and with the LPM kernel a new score based on lower partial moments.
--
--   **Formalization Note** The kernel $w$ is a measurable function (the paper also allows a local Borel measure such as $\delta_0$; that case, the quadratic score, is not covered). Assumption 1's "(2)/(3) is well-defined and finite" is formalized as explicit integrability hypotheses (see the `Setting` item). The printed "$f_{\mathbf y}*w$" in the theorem is read as $f_Y*w$, as on p. 8 above the theorem and on p. 32. "$P_Y$ is the unique minimizer" is expressed as strict inequality for every $P_X\ne P_Y$ in the class.
-- source:
--   Meng, Taylor, Ben Taieb, Li, Scores for Multivariate Distributions and Level Sets, arXiv:2002.09578v6, p. 8, Theorem 1; p. 32, Assumption 1

import Mathlib
import Definitions.Def_MultivarScores_L2Rule_Setting

namespace MultivarScores.L2Rule

open MeasureTheory

/-- Theorem 1, p. 8: under Assumption 1, the L² scoring rules (2) and (3) have the divergence (1),
are proper, and are strictly proper if `h` is nonzero `𝓛^d`-a.e. and `f_Y ∗ w` uniquely
characterizes every `P_Y ∈ 𝒱^d`. -/
theorem theorem_1 {d : ℕ} (w h : E d → ℝ) (𝒱 : Set (Measure (E d)))
    (hA : Assumption1 w h 𝒱) :
    (∀ PX ∈ 𝒱, ∀ PY ∈ 𝒱,
      (∫ y, S PX w h y ∂PY) - (∫ y, S PY w h y ∂PY) = L2div PX PY w h ∧
      (∫ y, S' PX w h y ∂PY) - (∫ y, S' PY w h y ∂PY) = L2div PX PY w h) ∧
    (∀ PX ∈ 𝒱, ∀ PY ∈ 𝒱,
      (∫ y, S PY w h y ∂PY) ≤ (∫ y, S PX w h y ∂PY) ∧
      (∫ y, S' PY w h y ∂PY) ≤ (∫ y, S' PX w h y ∂PY)) ∧
    ((∀ᵐ z, h z ≠ 0) → Characterizes w 𝒱 → ∀ PX ∈ 𝒱, ∀ PY ∈ 𝒱, PX ≠ PY →
      (∫ y, S PY w h y ∂PY) < (∫ y, S PX w h y ∂PY) ∧
      (∫ y, S' PY w h y ∂PY) < (∫ y, S' PX w h y ∂PY)) := by sorry

end MultivarScores.L2Rule
