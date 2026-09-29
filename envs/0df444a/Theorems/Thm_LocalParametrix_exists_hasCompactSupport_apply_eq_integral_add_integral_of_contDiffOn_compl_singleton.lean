-- Prove2me | Theorems.Thm_LocalParametrix_exists_hasCompactSupport_apply_eq_integral_add_integral_of_contDiffOn_compl_singleton
-- name    : LocalParametrix.exists_hasCompactSupport_apply_eq_integral_add_integral_of_contDiffOn_compl_singleton
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/cd61a13f-5616-5b79-9c14-3be28bcf143b
-- title:
--   Localising a fundamental kernel smooth off its pole
-- statement:
--   Let $E$ be a finite-dimensional real normed vector space, equipped with its Borel $\sigma$-algebra, and let $\mu$ be a measure on $E$ that is finite on compact sets. Let $D$ be an operator taking functions $E \to \mathbb{C}$ to functions $E \to \mathbb{C}$ which, restricted to the $C^\infty$ compactly supported functions, is additive ($D(F+G) = DF + DG$), takes continuous values, does not enlarge closed supports ($\operatorname{tsupp}(DF) \subseteq \operatorname{tsupp} F$), and admits transposes: for every $C^\infty$ compactly supported $g$ there is a continuous $h$ with $\operatorname{tsupp} h \subseteq \operatorname{tsupp} g$ and $\int_E (DF)\,g\,d\mu = \int_E F\,h\,d\mu$ for all $C^\infty$ compactly supported $F$. Let $x_0 \in E$, let $u, w \colon E \to \mathbb{C}$ be continuous with $u$ of class $C^\infty$ on the complement of $\{x_0\}$, and suppose $F(x_0) = \int_E (DF)\,u\,d\mu + \int_E F\,w\,d\mu$ for every $C^\infty$ compactly supported $F$. Then for every neighbourhood $V$ of $x_0$ there exist continuous, compactly supported $g_1, g_2 \colon E \to \mathbb{C}$ whose closed supports lie in $V$ and which satisfy the same reproducing identity $F(x_0) = \int_E (DF)\,g_1\,d\mu + \int_E F\,g_2\,d\mu$ for all $C^\infty$ compactly supported $F$.
--
--   This is the elementary localisation step in the construction of local parametrices: a globally defined kernel pair representing evaluation at $x_0$, with the singular member smooth away from $x_0$, is cut off to a pair supported in an arbitrarily small neighbourhood of $x_0$, at the cost of a continuous error term. It feeds the construction of a compactly supported reproducing identity for evaluation at a point in terms of $D$-iterates, used where a smoothing/approximation argument on a real vector space is required.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LocalParametrix_exists_hasCompactSupport_apply_eq_integral_add_integral_of_contDiffOn_compl_singleton.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Topology

theorem LocalParametrix.exists_hasCompactSupport_apply_eq_integral_add_integral_of_contDiffOn_compl_singleton
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    (D : (E → ℂ) → (E → ℂ))
    (hD_add : ∀ F G : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      ContDiff ℝ (⊤ : ℕ∞) G → HasCompactSupport G → D (F + G) = D F + D G)
    (hD_cont : ∀ F : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F → Continuous (D F))
    (hD_supp : ∀ F : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport (D F) ⊆ tsupport F)
    (hD_tr : ∀ g : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
      ∃ h : E → ℂ, Continuous h ∧ tsupport h ⊆ tsupport g ∧
        ∀ F : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
          ∫ x, D F x * g x ∂μ = ∫ x, F x * h x ∂μ)
    (x₀ : E) (u w : E → ℂ) (hu : Continuous u) (hw : Continuous w)
    (hu' : ContDiffOn ℝ (⊤ : ℕ∞) u {x₀}ᶜ)
    (hid : ∀ F : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      F x₀ = (∫ x, D F x * u x ∂μ) + ∫ x, F x * w x ∂μ)
    (V : Set E) (hV : V ∈ 𝓝 x₀) :
    ∃ g₁ g₂ : E → ℂ, Continuous g₁ ∧ Continuous g₂ ∧
      HasCompactSupport g₁ ∧ HasCompactSupport g₂ ∧ tsupport g₁ ⊆ V ∧ tsupport g₂ ⊆ V ∧
      ∀ F : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
        F x₀ = (∫ x, D F x * g₁ x ∂μ) + ∫ x, F x * g₂ x ∂μ := by sorry
