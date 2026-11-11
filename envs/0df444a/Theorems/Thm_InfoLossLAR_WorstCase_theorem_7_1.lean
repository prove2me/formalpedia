-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_theorem_7_1
-- name    : InfoLossLAR.WorstCase.theorem_7_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:02:07.263172+00:00
-- url     : https://prove2.me/theorems/41061813-842d-4e14-b57e-490dfc17fcd0
-- title:
--   Theorem 7.1 — stable finite-dimensional calibration
-- statement:
--   Let $V$ be a finite-dimensional real normed space, $(\Omega,\mu)$ a probability space, $Y$ a real vector space, and $\Psi:V\to L^1(\mu)$, $M:L^1(\mu)\to Y$, $E:V\to Y$ linear. Suppose a linear operator $A:V\to V$ satisfies
--   $$M\Psi=EA,\qquad\|A-I\|_{V\to V}\le\kappa<1 .$$
--   For every $\tau\in V$ there is a unique $z$ with $Az=\tau$, and $w=\Psi z$ satisfies $M(w)=E\tau$. For every reference $z_0\in V$, $\|z-z_0\|_V\le\|\tau-Az_0\|_V/(1-\kappa)$. If the constraints include total mass and the target mass is one, then $\mathbb E_\mu w=1$.
--
--   The principle is applied twice in §§8–9 (local and joint calibration) to construct the transport of Theorem 9.9.
--
--   Differences from the source:
--   - reading: "the constraints include total mass and the target mass is one" → for every linear functional $m$ on $Y$ with $m(M(w'))=\mathbb E_\mu w'$ for all $w'\in L^1(\mu)$ and $m(E\tau)=1$; reason: makes the informal phrase precise
--   - encoding: $A$ linear → a continuous linear map with the operator norm; reason: every linear map of a finite-dimensional normed space is continuous
-- source:
--   Chen Qian, Information Loss Is All You Need: TC⁰ Pseudorandomness from Worst-Case Lattices, arXiv:2611.05136 (held version, sha256 2ebdfbf3…), p. 30, Theorem 7.1

import Mathlib

set_option autoImplicit false

open MeasureTheory

namespace InfoLossLAR.WorstCase

/-- Theorem 7.1 (Stable finite-dimensional calibration), p. 30. `V` is a finite-dimensional real
normed space, `(Ω, μ)` a probability space, `Ψ : V → L¹(μ)` (synthesis), `M : L¹(μ) → Y`
(constraints, `Y` a real vector space) and `E : V → Y` (reference response) linear, and
`A : V → V` linear with `MΨ = EA` and `‖A − I‖ ≤ κ < 1` (operator norm). For every `τ ∈ V` there
is a unique `z` with `Az = τ`; `w = Ψz` satisfies `M(w) = Eτ`; `‖z − z_0‖ ≤ ‖τ − Az_0‖/(1 − κ)`
for every `z_0`; and if the constraints include total mass (a linear functional `m` of `Y` with
`m(M(w')) = E_μ w'` for every weight `w'`) and the target mass is one (`m(Eτ) = 1`), then
`E_μ w = 1`. -/
theorem theorem_7_1 {V Y Ω : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [AddCommGroup Y] [Module ℝ Y] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Ψ : V →ₗ[ℝ] Lp ℝ 1 μ) (M : Lp ℝ 1 μ →ₗ[ℝ] Y) (E : V →ₗ[ℝ] Y) (A : V →L[ℝ] V) (κ : ℝ)
    (hfac : M ∘ₗ Ψ = E ∘ₗ (A : V →ₗ[ℝ] V)) (hA : ‖A - ContinuousLinearMap.id ℝ V‖ ≤ κ)
    (hκ : κ < 1) (τ : V) :
    ∃ z : V, (A z = τ ∧ ∀ z' : V, A z' = τ → z' = z) ∧
      M (Ψ z) = E τ ∧
      (∀ z₀ : V, ‖z - z₀‖ ≤ ‖τ - A z₀‖ / (1 - κ)) ∧
      (∀ m : Y →ₗ[ℝ] ℝ, (∀ w' : Lp ℝ 1 μ, m (M w') = ∫ ω, w' ω ∂μ) → m (E τ) = 1 →
        ∫ ω, (Ψ z) ω ∂μ = 1) := by sorry

end InfoLossLAR.WorstCase
