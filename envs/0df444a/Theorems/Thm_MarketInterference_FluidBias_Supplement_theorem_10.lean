-- Prove2me | Theorems.Thm_MarketInterference_FluidBias_Supplement_theorem_10
-- name    : MarketInterference.FluidBias.Supplement.theorem_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T20:51:14.617118+00:00
-- url     : https://prove2.me/theorems/cf96eacd-77f8-468d-b4b0-edfa2056806d
-- title:
--   Theorem 10, p. 27 — under (v̄* − a⁰)·β ≥ (a⁰ − a¹)·β, Bias_SP ≤ Bias_RCT; under (a⁰ − a¹)·β = 0, Bias_SP = 0
-- statement:
--   Let $\mathcal G$ be a matching network with rates $\lambda\ge0$, $\lambda+\beta\ge0$, $\pi\ge0$ and any treatment fraction $\rho\in(0,1)$, under Assumption 2 (unique optimal primal and dual solutions of $\Phi(\lambda+\rho\beta,\pi)$) and Assumption 3 ($\beta\ge0$ or $\beta\le0$). Let $x^*$, $a^\rho$ be the optimal flow and the demand part of the optimal dual at $\lambda+\rho\beta$, $y^*$ any path decomposition of $x^*$, and $a^0$, $a^1$ the demand parts of optimal dual solutions of $\Phi(\lambda,\pi)$ (global control) and $\Phi(\lambda+\beta,\pi)$ (global treatment). Write $\mathrm{Bias}_{\mathrm{SP}}=|\hat\Delta_{\mathrm{SP}}-\Delta|$ and $\mathrm{Bias}_{\mathrm{RCT}}=|\hat\Delta_{\mathrm{RCT}}-\Delta|$. Then:
--
--   1. if
--   $$
--   (\bar v^*-a^0)\cdot\beta\ \ge\ (a^0-a^1)\cdot\beta, \tag{19}
--   $$
--   then $\mathrm{Bias}_{\mathrm{SP}}\le\mathrm{Bias}_{\mathrm{RCT}}$;
--   2. if $(a^0-a^1)\cdot\beta=0$ (20), then $\mathrm{Bias}_{\mathrm{SP}}=0$.
--
--   The condition compares interference in global control (average versus marginal value) with the change in marginal values between global control and global treatment.
--
--   **Formalization Note.** $a^0$ and $a^1$ may be any optimal dual solutions of the two end-point problems (they need not be unique). The paper's proof treats $\beta\ge0$ "without loss of generality"; the statement covers both signs.
-- source:
--   Bright, Delarue and Lobel, Reducing Marketplace Interference Bias Via Shadow Prices, arXiv:2205.02274v4, p. 27, Theorem 10, (19)–(20); proof pp. 56–57

import Mathlib
import Definitions.Def_MarketInterference_FluidBias_NetworkLP
import Definitions.Def_MarketInterference_FluidBias_PathFlow
import Definitions.Def_MarketInterference_FluidBias_Estimators

namespace MarketInterference.FluidBias.Supplement

/-- Theorem 10 (p. 27). For any treatment fraction `ρ ∈ (0, 1)`: let `a⁰` and `a¹` be the demand
parts of optimal dual solutions of `Φ(λ, π)` (global control) and `Φ(λ + β, π)` (global
treatment). If `(v̄* − a⁰) · β ≥ (a⁰ − a¹) · β` (19), then `|Δ̂_SP − Δ| ≤ |Δ̂_RCT − Δ|`; and if
`(a⁰ − a¹) · β = 0` (20), then `|Δ̂_SP − Δ| = 0`. Here `x`, `q` are the optimal primal and dual
solutions of `Φ(λ + ρβ, π)` (Assumption 2), `y` is any path decomposition of `x`, and `β` is
sign-consistent (Assumption 3). -/
theorem theorem_10 {nd ns : ℕ} {I E : Type} [Fintype I] [DecidableEq I] [Fintype E]
    [DecidableEq E]
    (N : Network nd ns I E) (lam beta : Fin nd → ℝ) (pi : Fin ns → ℝ) (ρ : ℝ)
    (hlam : 0 ≤ lam) (hlamb : 0 ≤ lam + beta) (hpi : 0 ≤ pi) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hsign : (∀ i, 0 ≤ beta i) ∨ (∀ i, beta i ≤ 0))
    (hA2p : ∃! x, IsOptimal N 1 (lam + ρ • beta) pi x)
    (hA2d : ∃! q, IsOptimalDual N 1 (lam + ρ • beta) pi q)
    (x : E → ℝ) (hx : IsOptimal N 1 (lam + ρ • beta) pi x)
    (y : SDPath N →₀ ℝ) (hy : IsPathDecomposition N y x)
    (q : DualVar nd ns I E) (hq : IsOptimalDual N 1 (lam + ρ • beta) pi q)
    (q0 q1 : DualVar nd ns I E) (hq0 : IsOptimalDual N 1 lam pi q0)
    (hq1 : IsOptimalDual N 1 (lam + beta) pi q1) :
    ((vbar lam beta ρ y - q0.a) ⬝ᵥ beta ≥ (q0.a - q1.a) ⬝ᵥ beta →
        |spFluid q beta - Delta N lam beta pi| ≤
          |rctFluid lam beta ρ y - Delta N lam beta pi|) ∧
      ((q0.a - q1.a) ⬝ᵥ beta = 0 → |spFluid q beta - Delta N lam beta pi| = 0) := by sorry

end MarketInterference.FluidBias.Supplement
