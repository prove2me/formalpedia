-- Prove2me | Theorems.Thm_MeasureTheory_exists_hasSum_mul_zpow_eval_mul_integral_prod_of_ae_forall_integral_mul_zpow_mul_eval_eq
-- name    : MeasureTheory.exists_hasSum_mul_zpow_eval_mul_integral_prod_of_ae_forall_integral_mul_zpow_mul_eval_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/e4da46f4-d9c7-5239-bce9-ba83319eb910
-- title:
--   Fibrewise functional equation transported through an outer integral
-- statement:
--   Let $X$, $T_1$, $T_2$ be measurable spaces carrying $s$-finite measures $m$, $\mu_1$, $\mu_2$, let $E_1 : X \times T_1 \to \mathbb{Z}$ and $E_2 : X \times T_2 \to \mathbb{Z}$ be measurable, and let $G_1 : X \times T_1 \to \mathbb{C}$, $G_2 : X \times T_2 \to \mathbb{C}$ be arbitrary functions. Let $a_1, b_1, a_2, b_2$ be real with $a_1 \ge 0$ and $a_2 \ge 0$, and assume that for each real $r$ with $a_i < r < b_i$ the function $p \mapsto G_i(p)\, r^{E_i(p)}$ is integrable for $m \otimes \mu_i$ ($i = 1, 2$). Let $Q_1, Q_2 \in \mathbb{C}[Y]$, $C \in \mathbb{C}$ and $k \in \mathbb{Z}$, and assume that for $m$-almost every $x \in X$ there are a polynomial $P \in \mathbb{C}[Y]$, an integer $n$ and reals $0 \le a_1' < b_1'$, $0 \le a_2' < b_2'$, all depending on $x$, such that for every $Y \in \mathbb{C}$ with $a_1' < \lVert Y \rVert < b_1'$ the function $t \mapsto G_1(x,t)\,Y^{E_1(x,t)}$ is $\mu_1$-integrable with $\bigl(\int_{T_1} G_1(x,t) Y^{E_1(x,t)}\,d\mu_1\bigr) Q_1(Y) = P(Y)\,Y^{n}$, and for every $Y$ with $a_2' < \lVert Y \rVert < b_2'$ the function $t \mapsto G_2(x,t)\,Y^{E_2(x,t)}$ is $\mu_2$-integrable with $\bigl(\int_{T_2} G_2(x,t) Y^{E_2(x,t)}\,d\mu_2\bigr) Q_2(Y) = C\,Y^{k}\,P(Y)\,Y^{n}$. The conclusion is the existence of a single family $e : \mathbb{Z} \to \mathbb{C}$ such that: $\sum_j \lVert e_j \rVert r^{j}$ converges for every real $r$ with $a_1 < r < b_1$; for every $Y$ with $a_1 < \lVert Y \rVert < b_1$ the family $j \mapsto e_j Y^{j}$ has sum $Q_1(Y) \int_{X \times T_1} G_1\, Y^{E_1}\, d(m \otimes \mu_1)$; $\sum_j \lVert C\, e_{j-k} \rVert r^{j}$ converges for every real $r$ with $a_2 < r < b_2$; and for every $Y$ with $a_2 < \lVert Y \rVert < b_2$ the family $j \mapsto C\, e_{j-k} Y^{j}$ has sum $Q_2(Y) \int_{X \times T_2} G_2\, Y^{E_2}\, d(m \otimes \mu_2)$.
--
--   This is the measure-theoretic transport step for Rankin–Selberg local integrals: a functional equation of rational-continuation type holding fibre by fibre, with denominators $Q_1, Q_2$ and monomial factor $C Y^{k}$ independent of the fibre, yields after clearing denominators one two-sided Laurent family whose sums compute both outer integrals, each on its own annulus, with no relation required between the fibrewise annuli and the annuli of convergence of the outer integrals. It is used in the local Rankin–Selberg computations for $\mathrm{GL}$ integrals against Whittaker functions, via the coefficient identity for $\sum_{i \in Q.\mathrm{support}}$ and the Laurent expansion of an integral $\int G\, Y^{E}$ supplied by the two cited results.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_exists_hasSum_mul_zpow_eval_mul_integral_prod_of_ae_forall_integral_mul_zpow_mul_eval_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.exists_hasSum_mul_zpow_eval_mul_integral_prod_of_ae_forall_integral_mul_zpow_mul_eval_eq
    {X T₁ T₂ : Type*} [MeasurableSpace X] [MeasurableSpace T₁] [MeasurableSpace T₂]
    (m : Measure X) (μ₁ : Measure T₁) (μ₂ : Measure T₂) [SFinite m] [SFinite μ₁] [SFinite μ₂]
    (E₁ : X × T₁ → ℤ) (hE₁ : Measurable E₁) (E₂ : X × T₂ → ℤ) (hE₂ : Measurable E₂)
    (G₁ : X × T₁ → ℂ) (G₂ : X × T₂ → ℂ)
    {a₁ b₁ a₂ b₂ : ℝ} (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂)
    (hG₁ : ∀ r : ℝ, a₁ < r → r < b₁ → Integrable (fun p => G₁ p * (r : ℂ) ^ E₁ p) (m.prod μ₁))
    (hG₂ : ∀ r : ℝ, a₂ < r → r < b₂ → Integrable (fun p => G₂ p * (r : ℂ) ^ E₂ p) (m.prod μ₂))
    (Q₁ Q₂ : Polynomial ℂ) (C : ℂ) (k : ℤ)
    (hfe : ∀ᵐ x ∂m, ∃ (P : Polynomial ℂ) (n : ℤ) (a₁' b₁' a₂' b₂' : ℝ),
      0 ≤ a₁' ∧ a₁' < b₁' ∧ 0 ≤ a₂' ∧ a₂' < b₂' ∧
      (∀ Y : ℂ, a₁' < ‖Y‖ → ‖Y‖ < b₁' →
        Integrable (fun t => G₁ (x, t) * Y ^ E₁ (x, t)) μ₁ ∧
        (∫ t, G₁ (x, t) * Y ^ E₁ (x, t) ∂μ₁) * Q₁.eval Y = P.eval Y * Y ^ n) ∧
      (∀ Y : ℂ, a₂' < ‖Y‖ → ‖Y‖ < b₂' →
        Integrable (fun t => G₂ (x, t) * Y ^ E₂ (x, t)) μ₂ ∧
        (∫ t, G₂ (x, t) * Y ^ E₂ (x, t) ∂μ₂) * Q₂.eval Y = C * Y ^ k * (P.eval Y * Y ^ n))) :
    ∃ e : ℤ → ℂ,
      (∀ r : ℝ, a₁ < r → r < b₁ → Summable fun j : ℤ => ‖e j‖ * r ^ j) ∧
      (∀ Y : ℂ, a₁ < ‖Y‖ → ‖Y‖ < b₁ →
        HasSum (fun j : ℤ => e j * Y ^ j) (Q₁.eval Y * ∫ p, G₁ p * Y ^ E₁ p ∂(m.prod μ₁))) ∧
      (∀ r : ℝ, a₂ < r → r < b₂ → Summable fun j : ℤ => ‖C * e (j - k)‖ * r ^ j) ∧
      (∀ Y : ℂ, a₂ < ‖Y‖ → ‖Y‖ < b₂ →
        HasSum (fun j : ℤ => C * e (j - k) * Y ^ j) (Q₂.eval Y * ∫ p, G₂ p * Y ^ E₂ p ∂(m.prod μ₂))) := by sorry
