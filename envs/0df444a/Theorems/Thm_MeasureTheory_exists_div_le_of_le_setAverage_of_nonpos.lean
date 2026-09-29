-- Prove2me | Theorems.Thm_MeasureTheory_exists_div_le_of_le_setAverage_of_nonpos
-- name    : MeasureTheory.exists_div_le_of_le_setAverage_of_nonpos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/5d359ad0-773d-5144-adbc-d21e8ea3fca8
-- title:
--   Point selection from a set average on a large subset
-- statement:
--   Let $\alpha$ be a measurable space with a measure $\mu$, let $s, E \subseteq \alpha$, let $\psi \colon \alpha \to \mathbb{R}$, and let $A, \theta \in \mathbb{R}$. Assume: $s$ is measurable; $\psi$ is integrable on $s$ with respect to $\mu$; $\psi(x) \le 0$ for every $x \in s$; $E \subseteq s$; $\mu(s) \neq 0$ and $\mu(s) \neq \infty$; $\theta > 0$; the measures of $s$ and $E$, taken as real numbers, satisfy $\theta \cdot \mu(s) \le \mu(E)$; and the set average of $\psi$ over $s$, namely $\mu(s)^{-1} \int_s \psi \, d\mu$, is at least $-A$. Then there exists $x \in E$ with $-A/\theta \le \psi(x)$. No measurability hypothesis on $E$ is imposed, and $A$ is not assumed non-negative (non-negativity follows from the other hypotheses).
--
--   This is the elementary first-moment selection step: a lower bound for the average of a non-positive function over $s$ yields, at some point of a subset $E$ of proportional measure at least $\theta$, the lower bound $-A/\theta$. It is stated for an arbitrary measure so as to cover both area averages over discs and arc-length averages over circles, and is used by [`MeasureTheory.exists_mem_le_of_setAverage_chain`](thm.html#MeasureTheory.exists_mem_le_of_setAverage_chain).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_exists_div_le_of_le_setAverage_of_nonpos.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem MeasureTheory.exists_div_le_of_le_setAverage_of_nonpos {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {s E : Set α} {ψ : α → ℝ} {A θ : ℝ}
    (hsm : MeasurableSet s) (hψ : MeasureTheory.IntegrableOn ψ s μ) (hψ0 : ∀ x ∈ s, ψ x ≤ 0)
    (hE : E ⊆ s) (hs0 : μ s ≠ 0) (hs : μ s ≠ ⊤) (hθ : 0 < θ) (hθE : θ * μ.real s ≤ μ.real E)
    (hA : -A ≤ ⨍ x in s, ψ x ∂μ) :
    ∃ x ∈ E, -A / θ ≤ ψ x := by sorry
