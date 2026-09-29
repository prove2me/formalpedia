-- Prove2me | Theorems.Thm_LocalParametrix_exists_continuous_hasCompactSupport_invariant_apply_eq_integral_add_integral_of_compactSpace
-- name    : LocalParametrix.exists_continuous_hasCompactSupport_invariant_apply_eq_integral_add_integral_of_compactSpace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/5d44fe13-aca1-5690-9d53-896d977eb3c9
-- title:
--   Averaging a local parametrix pair over a compact linear group
-- statement:
--   Let $E$ be a finite-dimensional real normed space, equipped with a Borel measurable structure and an additive Haar measure $\mu$, and let $G$ be a compact topological group. Let $\rho : G \to (E \to_{L[\mathbb{R}]} E)$ be a monoid homomorphism into the continuous linear endomorphisms of $E$ such that $(k,x) \mapsto \rho(k)x$ is jointly continuous, and let $x_0 \in E$ be fixed by every $\rho(k)$. Let $D$ be an operator on complex-valued functions on $E$ which carries every $C^\infty$ compactly supported $F$ to a continuous function, and which commutes with the action in the sense that $D(F \circ \rho(k)) = (DF) \circ \rho(k)$ for all $k \in G$ and all smooth compactly supported $F$. Assume further that every neighbourhood $W$ of $x_0$ contains a pair of continuous compactly supported $g_1, g_2 : E \to \mathbb{C}$ with $\operatorname{tsupport} g_i \subseteq W$ and $F(x_0) = \int_E DF \cdot g_1 \, d\mu + \int_E F \cdot g_2 \, d\mu$ for all smooth compactly supported $F$. Then for every neighbourhood $V$ of $x_0$ there exist continuous compactly supported $g_1, g_2$ with closed supports contained in $V$, invariant in the sense $g_i(\rho(k)x) = g_i(x)$ for all $k \in G$ and $x \in E$, and satisfying the same identity $F(x_0) = \int_E DF \cdot g_1 \, d\mu + \int_E F \cdot g_2 \, d\mu$ for every smooth compactly supported $F$.
--
--   This is the averaging step by which a local fundamental pair (a parametrix representation of evaluation at a fixed point, written as an integral against $DF$ plus a correction integral against $F$) is made invariant under a compact group of linear symmetries commuting with the operator $D$, as in Arthur's parametrix lemma. It is used in the construction of conjugation-invariant archimedean test data, feeding [`AutomorphicForm.exists_conjInvariant_forall_exists_eq_sum_integral_comp_mul_archEntries`](thm.html#AutomorphicForm.exists_conjInvariant_forall_exists_eq_sum_integral_comp_mul_archEntries).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LocalParametrix_exists_continuous_hasCompactSupport_invariant_apply_eq_integral_add_integral_of_compactSpace.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Topology

theorem LocalParametrix.exists_continuous_hasCompactSupport_invariant_apply_eq_integral_add_integral_of_compactSpace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (ρ : G →* (E →L[ℝ] E)) (hρ : Continuous fun p : G × E => ρ p.1 p.2)
    (x₀ : E) (hx₀ : ∀ k : G, ρ k x₀ = x₀)
    (D : (E → ℂ) → (E → ℂ))
    (hDc : ∀ F : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F → Continuous (D F))
    (hDρ : ∀ (k : G) (F : E → ℂ), ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      D (fun x => F (ρ k x)) = fun x => D F (ρ k x))
    (hex : ∀ W ∈ 𝓝 x₀, ∃ g₁ g₂ : E → ℂ, Continuous g₁ ∧ Continuous g₂ ∧
      HasCompactSupport g₁ ∧ HasCompactSupport g₂ ∧ tsupport g₁ ⊆ W ∧ tsupport g₂ ⊆ W ∧
      ∀ F : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
        F x₀ = (∫ x, D F x * g₁ x ∂μ) + ∫ x, F x * g₂ x ∂μ)
    (V : Set E) (hV : V ∈ 𝓝 x₀) :
    ∃ g₁ g₂ : E → ℂ, Continuous g₁ ∧ Continuous g₂ ∧
      HasCompactSupport g₁ ∧ HasCompactSupport g₂ ∧ tsupport g₁ ⊆ V ∧ tsupport g₂ ⊆ V ∧
      (∀ (k : G) (x : E), g₁ (ρ k x) = g₁ x) ∧ (∀ (k : G) (x : E), g₂ (ρ k x) = g₂ x) ∧
      ∀ F : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
        F x₀ = (∫ x, D F x * g₁ x ∂μ) + ∫ x, F x * g₂ x ∂μ := by sorry
