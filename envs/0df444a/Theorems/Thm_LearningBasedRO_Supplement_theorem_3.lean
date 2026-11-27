-- Prove2me | Theorems.Thm_LearningBasedRO_Supplement_theorem_3
-- name    : LearningBasedRO.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:17:15.198428+00:00
-- url     : https://prove2.me/theorems/d866b943-cd04-4274-bdf1-3950d3a6c01a
-- title:
--   Theorem 3 — feasibility guarantee for reconstruction: every feasible solution of (9) is feasible for (8)
-- statement:
--   Let $P$ be a probability measure on a measurable space $E$ (the law of $\xi$), $0<\epsilon<1$, $X$ a set of decisions, $g(x;\xi)=(g_j(x;\xi))_{j=1,\dots,l}\in\mathbb R^l$, $b\in\mathbb R^l$, and $k\in\mathbb R^l$ a positive vector. Let $\hat x_0\in X$ be any solution, with $\xi\mapsto g_j(\hat x_0;\xi)$ measurable for each $j$, and let $\rho$ be the $(1-\epsilon)$-quantile of $\max_{j=1,\dots,l}(g_j(\hat x_0;\xi)-b_j)/k_j$ under $P$. If $x$ is feasible for the reconstructed robust program (9), that is
--   $$g(x;\xi)\le b\quad\text{for every }\xi\text{ with }g(\hat x_0;\xi)\le b+\rho k,$$
--   then $x$ is feasible for the chance-constrained program (8):
--   $$P\big(g(x;\xi)\le b\big)\ge1-\epsilon .$$
--
--   This holds whether or not $\hat x_0$ is itself feasible for (8): (9) turns a possibly infeasible solution into a feasible one.
--
--   **Formalization Note** Inequalities in $\mathbb R^l$ are componentwise; $\rho$ is the lower quantile of the definition module `Reconstruction`.
--
--   Differences from the source:
--   - reading: ϵ (range not stated in the theorem) → 0 < ϵ < 1; reason: the paper's standing range (p.1, p.5)
--   - reading: ρ is the (1 − ϵ)-quantile of max_j (gⱼ(x̂₀; ξ) − bⱼ)/kⱼ → ρ = reconQuantile, the lower quantile inf{q : P(∀ j, (gⱼ(x̂₀; ξ) − bⱼ)/kⱼ ≤ q) ≥ 1 − ϵ}; reason: the standard (left-continuous inverse) quantile; Theorem 4's improvement clause needs exactly this one
--   - encoding: P(g(x̂₀; ξ) ≤ b + ρk), a probability of an event in ξ → hypothesis: ξ ↦ gⱼ(x̂₀; ξ) is measurable for every j; reason: it only excludes the case where that probability is undefined; nothing is assumed about g(x; ·) for other x
--   - encoding: max_{j=1,…,l} → 'for all j' inside the event; reason: the same event for l ≥ 1; avoids an empty maximum at l = 0
--   - generalization: x ∈ ℝᵈ, ξ ∈ ℝᵐ → arbitrary decision type X and measurable data space E, any probability measure P; reason: specializes to the paper's setting
-- source:
--   Hong–Huang–Lam, arXiv:1704.04342v2, Theorem 3, p.13

import Mathlib
import Definitions.Def_LearningBasedRO_Model
import Definitions.Def_LearningBasedRO_Supplement_Reconstruction

open MeasureTheory

namespace LearningBasedRO.Supplement

/-- **Theorem 3 (Feasibility guarantee for reconstruction).** Given any solution `x̂₀`, if `ρ` is the
`(1 - ϵ)`-quantile of `max_{j=1,…,l} (gⱼ(x̂₀; ξ) - bⱼ) / kⱼ`, then any feasible solution of the
reconstructed robust program (9) is also feasible for the chance-constrained program (8),
`P(g(x; ξ) ≤ b) ≥ 1 - ϵ`.
Hong–Huang–Lam, arXiv:1704.04342v2, Theorem 3, p.13.

**Formalization Note** `g(x; ξ) ∈ ℝˡ` is `g x ξ : Fin l → ℝ` with the componentwise order; (8) is
the base `CCPFeasible` with safety set `{y : y ≤ b}`; `k` is a positive vector (`kⱼ > 0`); `ρ` is
`reconQuantile`, the lower `(1 - ϵ)`-quantile. `x̂₀` is arbitrary (not necessarily feasible for (8)).
`ξ ↦ gⱼ(x̂₀; ξ)` is assumed measurable, which the page's `P(g(x̂₀; ξ) ≤ b + ρk)` presupposes;
nothing is assumed about `g(x; ·)` for other `x`. The decision set `X` and the data space `E`
are arbitrary (the page: `ℝᵈ`, `ℝᵐ`); `P` is a probability measure and `0 < ϵ < 1`. -/
theorem theorem_3 {X E : Type*} [MeasurableSpace E] (P : Measure E) [IsProbabilityMeasure P]
    (ϵ : ℝ) (hϵ0 : 0 < ϵ) (hϵ1 : ϵ < 1) {l : ℕ} (g : X → E → (Fin l → ℝ)) (b k : Fin l → ℝ)
    (hk : ∀ j, 0 < k j) (x₀ : X) (hg : ∀ j, Measurable fun ξ => g x₀ ξ j) (x : X)
    (hx : ReconFeasible P g b k ϵ x₀ x) : CCPFeasible P g (Set.Iic b) ϵ x := by sorry

end LearningBasedRO.Supplement
