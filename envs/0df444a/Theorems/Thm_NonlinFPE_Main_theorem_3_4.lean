-- Prove2me | Theorems.Thm_NonlinFPE_Main_theorem_3_4
-- name    : NonlinFPE.Main.theorem_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:29:42.595487+00:00
-- url     : https://prove2.me/theorems/313fbdcb-0980-4095-9840-3509b5ef6e4f
-- title:
--   Theorem 3.4, p. 18 — under (H1)–(H3), for each u₀ ∈ L¹ there is a unique weak (mild) solution of (3.1), with (3.36)–(3.39)
-- statement:
--   Assume (H1)–(H3) and let $A$ be the operator (3.8)–(3.9) on $L^1 = L^1(\mathbb R^d)$. A **weak solution** of the nonlinear Fokker–Planck equation
--   $$\frac{\partial u}{\partial t} - \sum_{i,j=1}^d D^2_{ij}\big(a_{ij}(x,u)u\big) + \operatorname{div}\big(b(x,u)u\big) = 0, \qquad u(0,x) = u_0(x), \tag{3.1}$$
--   is a mild solution of $u' + Au = 0$, $u(0) = u_0$ (3.2) in $L^1$. Then for each $u_0 \in L^1$ there is a unique weak solution $u = u(\cdot,u_0) \in C([0,\infty);L^1)$, and
--
--   1. $|u(t,u_0^1) - u(t,u_0^2)|_1 \le |u_0^1 - u_0^2|_1$ for $u_0^1, u_0^2 \in L^1$, $t \ge 0$; (3.36)
--   2. $u \ge 0$ a.e. if $u_0 \ge 0$ a.e.; (3.37)
--   3. $\int u(t,x)\,dx = \int u_0(x)\,dx$ for $t \ge 0$; (3.38)
--   4. $u$ solves (3.1) in $\mathcal D'((0,\infty)\times\mathbb R^d)$ in the sense (3.39).
--
--   This is the paper's first main existence result for the nonlinear FPE and the PDE input of Theorem 4.1 in the nondegenerate case.
--
--   **Formalization Note** (3.37) is stated as $u(t) \ge 0$ a.e. on $\mathbb R^d$ for every $t \ge 0$; for $u \in C([0,\infty);L^1)$ this is equivalent to $u \ge 0$ a.e. on $(0,\infty)\times\mathbb R^d$. Uniqueness is in the class of mild solutions, not of distributional solutions.
-- source:
--   Barbu, Röckner, From nonlinear Fokker-Planck equations to solutions of distribution dependent SDE, arXiv:1808.10706v4, Theorem 3.4, p. 18, (3.36)–(3.39)

import Mathlib
import Definitions.Def_NonlinFPE_Main_Setting
import Definitions.Def_NonlinFPE_Main_MAccretive

open MeasureTheory
open scoped NNReal

namespace NonlinFPE.Main

open EthierKurtz

/-- Theorem 3.4, p. 18, under (H1)–(H3): for each `u₀ ∈ L¹` there is a unique weak (= mild)
solution `u ∈ C([0, ∞); L¹)` of (3.1); mild solutions satisfy the contraction (3.36), positivity
(3.37), mass conservation (3.38), and solve (3.1) in `𝒟′((0, ∞) × ℝᵈ)` in the sense (3.39). -/
theorem theorem_3_4 {d : ℕ} (a : Fin d → Fin d → SDEState d → ℝ → ℝ)
    (b : Fin d → SDEState d → ℝ → ℝ) (γ : ℝ) (hND : HypND a b γ) :
    (∀ u₀ : SDEState d →₁[volume] ℝ,
      ∃! u : ℝ≥0 → SDEState d →₁[volume] ℝ, IsMildSolution (opA a b) u₀ u) ∧
    (∀ (u₀₁ u₀₂ : SDEState d →₁[volume] ℝ) (u₁ u₂ : ℝ≥0 → SDEState d →₁[volume] ℝ),
      IsMildSolution (opA a b) u₀₁ u₁ → IsMildSolution (opA a b) u₀₂ u₂ →
        ∀ t, ‖u₁ t - u₂ t‖ ≤ ‖u₀₁ - u₀₂‖) ∧
    (∀ (u₀ : SDEState d →₁[volume] ℝ) (u : ℝ≥0 → SDEState d →₁[volume] ℝ),
      IsMildSolution (opA a b) u₀ u → 0 ≤ᵐ[volume] (u₀ : SDEState d → ℝ) →
        ∀ t, 0 ≤ᵐ[volume] (u t : SDEState d → ℝ)) ∧
    (∀ (u₀ : SDEState d →₁[volume] ℝ) (u : ℝ≥0 → SDEState d →₁[volume] ℝ),
      IsMildSolution (opA a b) u₀ u → ∀ t, ∫ x, u t x = ∫ x, u₀ x) ∧
    (∀ (u₀ : SDEState d →₁[volume] ℝ) (u : ℝ≥0 → SDEState d →₁[volume] ℝ),
      IsMildSolution (opA a b) u₀ u → IsDistribSolution a b u) := by sorry

end NonlinFPE.Main
