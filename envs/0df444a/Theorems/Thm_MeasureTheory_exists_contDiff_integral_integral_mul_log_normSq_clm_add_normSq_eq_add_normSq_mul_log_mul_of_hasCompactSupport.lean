-- Prove2me | Theorems.Thm_MeasureTheory_exists_contDiff_integral_integral_mul_log_normSq_clm_add_normSq_eq_add_normSq_mul_log_mul_of_hasCompactSupport
-- name    : MeasureTheory.exists_contDiff_integral_integral_mul_log_normSq_clm_add_normSq_eq_add_normSq_mul_log_mul_of_hasCompactSupport
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/75a46622-6ad9-53c4-8db2-51bd5f4dd3a7
-- title:
--   Parametric log-potential along a moving linear form: smooth plus ‖r‖²log‖r‖ term
-- statement:
--   Let $P$ and $V$ be finite-dimensional real normed spaces, with $V$ equipped with its Borel $\sigma$-algebra, and let $\mu$ be an additive Haar measure on $V$. Let $g : P \times (\mathbb{C} \times V) \to \mathbb{C}$ be smooth in the real sense (i.e. $C^\infty$ over $\mathbb{R}$) with compact support, let $L : P \to (\mathbb{C} \to_{L[\mathbb{R}]} \mathbb{C})$ be a smooth family of continuous $\mathbb{R}$-linear endomorphisms of $\mathbb{C}$ each of which is injective (if $L(p)z = 0$ then $z = 0$), and let $\varphi : P \to (V \to_{L[\mathbb{R}]} \mathbb{C})$ be a smooth family of continuous $\mathbb{R}$-linear maps $V \to \mathbb{C}$. Then there exist functions $A, B : P \times \mathbb{C} \to \mathbb{C}$, both $C^\infty$ over $\mathbb{R}$, such that for every $p \in P$ and every $r \in \mathbb{C}$ the function $(z,v) \mapsto g(p,(z,v)) \cdot \log\big(\|L(p)z + \varphi(p)v\|^2 + \|r\|^2\big)$ is integrable for the product of Lebesgue measure on $\mathbb{C}$ with $\mu$, and its integral equals $A(p,r) + \big(\|r\|^2 \log \|r\|\big)\, B(p,r)$, the real scalar being viewed in $\mathbb{C}$.
--
--   This isolates the exact singular behaviour in the offset $r$ of a logarithmic potential integrated against a compactly supported smooth density, in the presence of a smoothly varying injective $\mathbb{R}$-linear form $L(p)z + \varphi(p)v$ on $\mathbb{C} \times V$: the result is a smooth function of $(p,r)$ plus the planar kink $\|r\|^2\log\|r\|$ times another smooth function. It feeds the analysis of archimedean integrals at a complex place, being used in the construction of smooth compactly supported data for the corresponding kernel integral.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_exists_contDiff_integral_integral_mul_log_normSq_clm_add_normSq_eq_add_normSq_mul_log_mul_of_hasCompactSupport.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.exists_contDiff_integral_integral_mul_log_normSq_clm_add_normSq_eq_add_normSq_mul_log_mul_of_hasCompactSupport
    {P V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure]
    (g : P × (ℂ × V) → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g)
    (L : P → (ℂ →L[ℝ] ℂ)) (hL : ContDiff ℝ (⊤ : ℕ∞) L) (hL0 : ∀ (p : P) (z : ℂ), L p z = 0 → z = 0)
    (φ : P → (V →L[ℝ] ℂ)) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ∃ A B : P × ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) A ∧ ContDiff ℝ (⊤ : ℕ∞) B ∧
      ∀ (p : P) (r : ℂ),
        Integrable (fun zv : ℂ × V =>
          g (p, zv) * (Real.log (‖L p zv.1 + φ p zv.2‖ ^ 2 + ‖r‖ ^ 2) : ℂ)) ((volume : Measure ℂ).prod μ) ∧
        ∫ zv : ℂ × V, g (p, zv) * (Real.log (‖L p zv.1 + φ p zv.2‖ ^ 2 + ‖r‖ ^ 2) : ℂ) ∂((volume : Measure ℂ).prod μ) =
          A (p, r) + ((‖r‖ ^ 2 * Real.log ‖r‖ : ℝ) : ℂ) * B (p, r) := by sorry
