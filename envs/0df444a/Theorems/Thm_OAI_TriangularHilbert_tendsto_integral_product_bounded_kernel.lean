-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_tendsto_integral_product_bounded_kernel
-- name    : OAI.TriangularHilbert.tendsto_integral_product_bounded_kernel
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:32:24.420893+00:00
-- url     : https://prove2.me/theorems/0f3c3cdd-ac5b-4b28-8608-3b9dafa637f5
-- title:
--   Dominated convergence for products against a bounded kernel
-- statement:
--   Let $F_n,G_n:\mathbb R\to\mathbb C$ be measurable with $F_n\to f$ and $G_n\to g$ almost everywhere. Suppose $|F_n|^3\le D$ and $|G_n|^3\le E$ almost everywhere for all $n$, with $D,E$ integrable. Let $K$ be measurable with $|K|\le L$ and $K=0$ outside a measurable set $s$ of finite measure. Then
--   $$
--   \int F_n(c)\,G_n(c)\,K(c)\,dc\ \longrightarrow\ \int f(c)\,g(c)\,K(c)\,dc .
--   $$
--
--   Cubic domination of the factors suffices for convergence against a bounded kernel of finite-measure support.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/CubicProduct.lean#L49-L70

import Mathlib
import Definitions.Def_TriangularHilbert

open OAI OAI.TriangularHilbert
open MeasureTheory Filter
open scoped Topology

theorem OAI.TriangularHilbert.tendsto_integral_product_bounded_kernel (f g : ℝ → ℂ) (F G : ℕ → ℝ → ℂ) (K : ℝ → ℝ)
    (hF : ∀ n, AEStronglyMeasurable (F n) volume) (hG : ∀ n, AEStronglyMeasurable (G n) volume)
    (hK : Measurable K) {D E : ℝ → ℝ} (hD : Integrable D) (hE : Integrable E)
    (hbound : ∀ᵐ c : ℝ, ∀ n, ‖F n c‖^3 ≤ D c ∧ ‖G n c‖^3 ≤ E c)
    (ht : ∀ᵐ c : ℝ, Tendsto (fun n => F n c) atTop (𝓝 (f c)) ∧ Tendsto (fun n => G n c) atTop (𝓝 (g c)))
    {s : Set ℝ} (hs : MeasurableSet s) (hμ : volume s ≠ ⊤) {L : ℝ} (hL : 0 ≤ L)
    (hk : ∀ c, |K c| ≤ L) (hzero : ∀ c ∉ s, K c = 0) :
    Tendsto (fun n => ∫ c : ℝ, F n c*G n c*(K c:ℂ)) atTop
      (𝓝 (∫ c : ℝ, f c*g c*(K c:ℂ))) := by sorry
