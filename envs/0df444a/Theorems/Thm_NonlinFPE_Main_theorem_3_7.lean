-- Prove2me | Theorems.Thm_NonlinFPE_Main_theorem_3_7
-- name    : NonlinFPE.Main.theorem_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:30:19.969697+00:00
-- url     : https://prove2.me/theorems/30efc5ba-0cc8-4873-81fb-08999448cc59
-- title:
--   Theorem 3.7, p. 22 — under (H1)′–(H3)′, for each u₀ ∈ L¹ there is a unique weak (mild) solution of (3.41), with (3.36)–(3.39)
-- statement:
--   Assume (H1)′–(H3)′ and let $A_1$ be the operator (3.42). A weak solution of
--   $$u_t - \sum_{i,j=1}^d D^2_{ij}\big(a_{ij}(u)u\big) + \sum_{i=1}^d D_i\big(b_i(u)u\big) = 0, \qquad u(0,x) = u_0(x), \tag{3.41}$$
--   is a mild solution of $u' + A_1u = 0$, $u(0) = u_0$ in $L^1$. Then for each $u_0 \in L^1$ there is a unique weak solution $u = u(t,u_0) \in C([0,\infty);L^1)$; it satisfies the contraction (3.36), positivity (3.37) and mass conservation (3.38), and solves (3.41) in $\mathcal D'((0,\infty)\times\mathbb R^d)$ in the sense of (3.39).
--
--   This is the PDE input of Theorem 4.1 in the degenerate case.
--
--   **Formalization Note** As in Theorem 3.4: $A_1$ is the operator $A$ with coefficients constant in $x$, (3.37) is stated for every $t$, and uniqueness is among mild solutions.
-- source:
--   Barbu, Röckner, From nonlinear Fokker-Planck equations to solutions of distribution dependent SDE, arXiv:1808.10706v4, Theorem 3.7, p. 22, with (3.41)–(3.42), pp. 19–20, and (3.36)–(3.39), p. 18

import Mathlib
import Definitions.Def_NonlinFPE_Main_Setting
import Definitions.Def_NonlinFPE_Main_MAccretive

open MeasureTheory
open scoped NNReal

namespace NonlinFPE.Main

open EthierKurtz

/-- Theorem 3.7, p. 22, under (H1)′–(H3)′: for each `u₀ ∈ L¹` there is a unique weak (= mild, for
the operator `A₁` of (3.42)) solution `u ∈ C([0, ∞); L¹)` of (3.41); mild solutions satisfy
(3.36)–(3.38) and solve (3.41) in `𝒟′((0, ∞) × ℝᵈ)` in the sense (3.39). -/
theorem theorem_3_7 {d : ℕ} (a' : Fin d → Fin d → ℝ → ℝ) (b' : Fin d → ℝ → ℝ)
    (hDeg : HypDeg a' b') :
    (∀ u₀ : SDEState d →₁[volume] ℝ,
      ∃! u : ℝ≥0 → SDEState d →₁[volume] ℝ, IsMildSolution (opA (liftA a') (liftB b')) u₀ u) ∧
    (∀ (u₀₁ u₀₂ : SDEState d →₁[volume] ℝ) (u₁ u₂ : ℝ≥0 → SDEState d →₁[volume] ℝ),
      IsMildSolution (opA (liftA a') (liftB b')) u₀₁ u₁ → IsMildSolution (opA (liftA a') (liftB b')) u₀₂ u₂ →
        ∀ t, ‖u₁ t - u₂ t‖ ≤ ‖u₀₁ - u₀₂‖) ∧
    (∀ (u₀ : SDEState d →₁[volume] ℝ) (u : ℝ≥0 → SDEState d →₁[volume] ℝ),
      IsMildSolution (opA (liftA a') (liftB b')) u₀ u → 0 ≤ᵐ[volume] (u₀ : SDEState d → ℝ) →
        ∀ t, 0 ≤ᵐ[volume] (u t : SDEState d → ℝ)) ∧
    (∀ (u₀ : SDEState d →₁[volume] ℝ) (u : ℝ≥0 → SDEState d →₁[volume] ℝ),
      IsMildSolution (opA (liftA a') (liftB b')) u₀ u → ∀ t, ∫ x, u t x = ∫ x, u₀ x) ∧
    (∀ (u₀ : SDEState d →₁[volume] ℝ) (u : ℝ≥0 → SDEState d →₁[volume] ℝ),
      IsMildSolution (opA (liftA a') (liftB b')) u₀ u → IsDistribSolution (liftA a') (liftB b') u) := by sorry

end NonlinFPE.Main
