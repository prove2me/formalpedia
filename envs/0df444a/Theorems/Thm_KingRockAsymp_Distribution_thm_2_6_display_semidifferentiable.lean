-- Prove2me | Theorems.Thm_KingRockAsymp_Distribution_thm_2_6_display_semidifferentiable
-- name    : KingRockAsymp.Distribution.thm_2_6_display_semidifferentiable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:06:20.916435+00:00
-- url     : https://prove2.me/theorems/c4f67f3f-b166-4684-8e47-b5e63df2297e
-- title:
--   Proof of Theorem 2.6, display (p. 8) — semi-differentiability of the solution map (cited from [12], Thm 4.1 and Rem. 4.3)
-- statement:
--   Let $Z$ be a separable Banach space and assume the analytical assumptions M.1–M.4 at $(z^*,x^*)$ for $f : Z \times \mathbb R^n \to \mathbb R^m$ and $N : \mathbb R^n \rightrightarrows \mathbb R^m$, with strong partial B-derivative $D_z f(z^*,x^*)$, and let $F = f(z^*,\cdot) + N$ and $J(z) = \{x \mid 0 \in f(z,x) + N(x)\}$. Then there is a compact neighborhood $U$ of $x^*$ such that the localized solution map $z \mapsto U \cap J(z)$ is semi-differentiable at $(z^*,x^*)$, with derivative
--   $$DJ(z^*|x^*)(w) = DF^{-1}(0|x^*)\big(-D_z f(z^*,x^*)(w)\big) \qquad \text{for every } w \in Z.$$
--
--   This is the generalized implicit function theorem behind the paper's asymptotics: it identifies the first-order behaviour of the solutions under perturbations of the data with the contingent derivative of $F^{-1}$. The paper cites it from [12] (Theorem 4.1 and Remark 4.3).
--
--   **Formalization Note** "$J$ … at the pair $(z^*,x^*)$" with the compact neighborhood $U$ is read as the localized map $z \mapsto U \cap J(z)$, which is the map the paper's proof goes on to use ($\tau_\nu^{-1}[U \cap J(z^\nu) - x^*]$); both its semi-differentiability (2.3) and the formula for its contingent derivative (2.2) are asserted.
-- source:
--   King & Rockafellar, Asymptotic Theory for Solutions in Statistical Estimation and Stochastic Programming, Math. Oper. Res. 18(1) (1993), proof of Theorem 2.6, display, p. 8 (authors' manuscript pagination); cited from [12], Theorem 4.1 and Remark 4.3

import Mathlib
import Definitions.Def_KingRockAsymp_Distribution_Basic

namespace KingRockAsymp.Distribution

open Set Filter Topology Metric MeasureTheory ProbabilityTheory

theorem thm_2_6_display_semidifferentiable {Z : Type*} [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [CompleteSpace Z] [TopologicalSpace.SeparableSpace Z] {n m : ℕ}
    (f : Z → Rn n → Rn m) (N : Rn n → Set (Rn m)) (z₀ : Z) (x₀ : Rn n) (Dz : Z → Rn m)
    (hM : AnalyticalAssumptions f N z₀ x₀ Dz) :
    ∃ U : Set (Rn n), IsCompact U ∧ U ∈ 𝓝 x₀ ∧
      IsSemiDifferentiable (fun z => U ∩ solMap f N z) z₀ x₀ ∧
      ∀ w : Z, contingentDeriv (fun z => U ∩ solMap f N z) z₀ x₀ w =
        contingentDeriv (svInv (fPlusN f N z₀)) 0 x₀ (-(Dz w)) := by sorry

end KingRockAsymp.Distribution
