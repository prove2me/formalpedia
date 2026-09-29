-- Prove2me | Theorems.Thm_MeasureTheory_differentiableOn_integral_of_forall_differentiableOn_of_locally_norm_le
-- name    : MeasureTheory.differentiableOn_integral_of_forall_differentiableOn_of_locally_norm_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/a5352f04-1668-5929-a198-226715b32025
-- title:
--   Holomorphy of a locally dominated parametric integral
-- statement:
--   Let $Y$ be a measurable space carrying a measure $\nu$, let $U \subseteq \mathbb{C}$ be open, and let $F : \mathbb{C} \to Y \to \mathbb{C}$ be a function of two variables. Assume: (i) for every $z \in U$ the slice $F(z,\cdot)$ is almost everywhere strongly measurable with respect to $\nu$; (ii) for every $a \in Y$ the function $z \mapsto F(z,a)$ is complex differentiable on $U$ in the sense of `DifferentiableOn`, i.e. differentiable within $U$ at each point of $U$; and (iii) local uniform domination: for every $z_0 \in U$ there are a radius $\varepsilon > 0$ and a $\nu$-integrable function $M : Y \to \mathbb{R}$ such that $\|F(z,a)\| \le M(a)$ for all $z$ in the open ball of radius $\varepsilon$ about $z_0$ and all $a \in Y$ (the bound is required at every point of $Y$, not merely almost everywhere, and the ball is not required to lie inside $U$). Then the parametric integral $z \mapsto \int_Y F(z,a)\,d\nu(a)$ is complex differentiable on $U$.
--
--   This is the standard holomorphy criterion for integrals depending holomorphically on a parameter (differentiation under the integral sign in the holomorphic case), in the form of local domination by an integrable majorant. It is used in the analytic part of the Rankin–Selberg and Petersson-inner-product constructions, for instance to establish holomorphy of integrals over an archimedean torus and of axis integrals against a cusp-form basis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_differentiableOn_integral_of_forall_differentiableOn_of_locally_norm_le.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.differentiableOn_integral_of_forall_differentiableOn_of_locally_norm_le
    {Y : Type*} [MeasurableSpace Y] (ν : Measure Y)
    {U : Set ℂ} (hU : IsOpen U) (F : ℂ → Y → ℂ)
    (hmeas : ∀ z ∈ U, AEStronglyMeasurable (F z) ν)
    (hhol : ∀ a : Y, DifferentiableOn ℂ (fun z => F z a) U)
    (hdom : ∀ z₀ ∈ U, ∃ ε : ℝ, 0 < ε ∧ ∃ M : Y → ℝ, Integrable M ν ∧
      ∀ z ∈ Metric.ball z₀ ε, ∀ a : Y, ‖F z a‖ ≤ M a) :
    DifferentiableOn ℂ (fun z => ∫ a, F z a ∂ν) U := by sorry
