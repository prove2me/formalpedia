-- Prove2me | Theorems.Thm_LearningBasedRO_Supplement_theorem_4
-- name    : LearningBasedRO.Supplement.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:17:45.048352+00:00
-- url     : https://prove2.me/theorems/385593a7-45e4-4cd6-9edf-6a9af6a5f30e
-- title:
--   Theorem 4 — monotonic objective improvement: an optimal solution $\hat x$ of (9) is feasible for (8), and $f(\hat x)\le f(\hat x_0)$ when $\hat x_0$ is
-- statement:
--   Under the assumptions of Theorem 3 ($P$ a probability measure, $0<\epsilon<1$, $k$ a positive vector, $\xi\mapsto g_j(\hat x_0;\xi)$ measurable, $\rho$ the $(1-\epsilon)$-quantile of $\max_j(g_j(\hat x_0;\xi)-b_j)/k_j$), let $f:X\to\mathbb R$ be the objective and $\hat x$ an optimal solution of the reconstructed robust program
--   $$\text{minimize } f(x)\ \text{ subject to }\ g(x;\xi)\le b\quad\forall\,\xi:\ g(\hat x_0;\xi)\le b+\rho k. \tag{9}$$
--   Then
--
--   1. $\hat x$ is feasible for (8): $P(g(\hat x;\xi)\le b)\ge1-\epsilon$;
--   2. if $\hat x_0$ is feasible for (8), then $f(\hat x)\le f(\hat x_0)$.
--
--   Together with Theorem 3 this makes (9) a self-improving step: an infeasible input becomes feasible, and a feasible input is not made worse.
--
--   **Formalization Note** "An optimal solution of (9)" is a hypothesis on $\hat x$ (written `xhat` in Lean); existence is not claimed.
--
--   Differences from the source:
--   - reading: ϵ (range not stated in the theorem) → 0 < ϵ < 1; reason: the paper's standing range (p.1, p.5)
--   - reading: ρ is the (1 − ϵ)-quantile of max_j (gⱼ(x̂₀; ξ) − bⱼ)/kⱼ → ρ = reconQuantile, the lower quantile inf{q : P(∀ j, (gⱼ(x̂₀; ξ) − bⱼ)/kⱼ ≤ q) ≥ 1 − ϵ}; reason: the standard (left-continuous inverse) quantile; Theorem 4's improvement clause needs exactly this one
--   - encoding: P(g(x̂₀; ξ) ≤ b + ρk), a probability of an event in ξ → hypothesis: ξ ↦ gⱼ(x̂₀; ξ) is measurable for every j; reason: it only excludes the case where that probability is undefined; nothing is assumed about g(x; ·) for other x
--   - encoding: max_{j=1,…,l} → 'for all j' inside the event; reason: the same event for l ≥ 1; avoids an empty maximum at l = 0
--   - generalization: x ∈ ℝᵈ, ξ ∈ ℝᵐ → arbitrary decision type X and measurable data space E, any probability measure P; reason: specializes to the paper's setting
--   - encoding: an optimal solution x̂ of (9) → hypothesis IsReconOptimal: x̂ feasible for (9) and f(x̂) ≤ f(x) for every x feasible for (9); reason: the definition of an optimal solution; its existence is not claimed by the source
-- source:
--   Hong–Huang–Lam, arXiv:1704.04342v2, Theorem 4, p.13

import Mathlib
import Definitions.Def_LearningBasedRO_Model
import Definitions.Def_LearningBasedRO_Supplement_Reconstruction

open MeasureTheory

namespace LearningBasedRO.Supplement

/-- **Theorem 4 (Monotonic objective improvement).** Under the same assumption as Theorem 3, an
optimal solution `x̂` of the reconstructed robust program (9) is feasible for the chance-constrained
program (8). Moreover, if `x̂₀` is feasible for (8), then `f(x̂) ≤ f(x̂₀)`.
Hong–Huang–Lam, arXiv:1704.04342v2, Theorem 4, p.13.

**Formalization Note** Same encoding as Theorem 3 (`reconQuantile` is the lower
`(1 - ϵ)`-quantile, `kⱼ > 0`, `ξ ↦ gⱼ(x̂₀; ξ)` measurable, `X`, `E` arbitrary, `0 < ϵ < 1`).
`xhat` stands for `x̂`; "an optimal solution of (9)" is the hypothesis `IsReconOptimal`
(feasible for (9) and `f(x̂) ≤ f(x)` for all `x` feasible for (9)); existence is not claimed. -/
theorem theorem_4 {X E : Type*} [MeasurableSpace E] (P : Measure E) [IsProbabilityMeasure P]
    (ϵ : ℝ) (hϵ0 : 0 < ϵ) (hϵ1 : ϵ < 1) {l : ℕ} (g : X → E → (Fin l → ℝ)) (b k : Fin l → ℝ)
    (hk : ∀ j, 0 < k j) (x₀ : X) (hg : ∀ j, Measurable fun ξ => g x₀ ξ j) (f : X → ℝ)
    (xhat : X) (hopt : IsReconOptimal P g b k ϵ x₀ f xhat) :
    CCPFeasible P g (Set.Iic b) ϵ xhat ∧
      (CCPFeasible P g (Set.Iic b) ϵ x₀ → f xhat ≤ f x₀) := by sorry

end LearningBasedRO.Supplement
