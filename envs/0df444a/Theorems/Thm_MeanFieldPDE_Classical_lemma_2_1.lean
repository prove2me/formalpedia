-- Prove2me | Theorems.Thm_MeanFieldPDE_Classical_lemma_2_1
-- name    : MeanFieldPDE.Classical.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:07:17.540991+00:00
-- url     : https://prove2.me/theorems/3bf1ae65-256e-4034-a014-7089c419bc4a
-- title:
--   Lemma 2.1, p. 6 — second-order expansion of f ∈ C^{2,1}_b(P₂(ℝ^d)) with remainder C·E[|ϑ−ϑ₀|³ ∧ |ϑ−ϑ₀|²]
-- statement:
--   Let $f\in C^{2,1}_b(\mathcal P_2(\mathbb R^d))$ with derivatives $\partial_\mu f$, $\partial^2_\mu f$ and $\partial_y\partial_\mu f$. There is a constant $C\ge0$ such that for all $\vartheta_0,\vartheta\in L^2(\mathcal F;\mathbb R^d)$, writing $\eta=\vartheta-\vartheta_0$,
--   $$f(P_\vartheta)-f(P_{\vartheta_0})=E[\partial_\mu f(P_{\vartheta_0},\vartheta_0)\cdot\eta]+\tfrac12E\big[\tilde E[\mathrm{tr}(\partial^2_\mu f(P_{\vartheta_0},\widetilde{\vartheta_0},\vartheta_0)\cdot\tilde\eta\otimes\eta)]\big]+\tfrac12E[\partial_y\partial_\mu f(P_{\vartheta_0},\vartheta_0)\cdot\eta\otimes\eta]+R,$$
--   $$|R|\le C\,E\big[|\vartheta-\vartheta_0|^3\wedge|\vartheta-\vartheta_0|^2\big].$$
--   Here $(\tilde\vartheta_0,\tilde\eta)$ is an independent copy of $(\vartheta_0,\eta)$, and the trace term is $\sum_{i,j}[\partial_\mu((\partial_\mu f)_j(\cdot,\vartheta_0))(P_{\vartheta_0},\tilde\vartheta_0)]_i\,\tilde\eta_i\,\eta_j$.
--
--   This expansion on the Wasserstein space is the analytic input of the mean-field Itô formula (Proposition 6.1).
--
--   **Formalization Note** $E\tilde E$ is the iterated integral over $P\otimes P$, the inner variable $\omega'$ carrying the tilde. The constant is uniform in $\vartheta_0$ and $\vartheta$. The statement is on the paper's space (the standing setting), where the Lions derivative is defined.
-- source:
--   Buckdahn, Li, Peng & Rainer, Mean-field stochastic differential equations and associated PDEs, arXiv:1407.1215v1, p. 6, Lemma 2.1, (2.5)–(2.6)

import Mathlib
import Definitions.Def_MeanFieldPDE_Classical_Setting
import Definitions.Def_MeanFieldPDE_Classical_Lions

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace MeanFieldPDE.Classical

/-- Lemma 2.1, p. 6 (second-order expansion on `P₂(ℝ^d)`): for `f ∈ C^{2,1}_b(P₂(ℝ^d))` there is a
constant `C ≥ 0` such that for all `ϑ₀, ϑ ∈ L²(F; ℝ^d)`, with `η = ϑ − ϑ₀`,
`f(P_ϑ) − f(P_{ϑ₀}) = E[∂_μ f(P_{ϑ₀}, ϑ₀)·η] + ½ E[Ẽ[tr(∂²_μ f(P_{ϑ₀}, ϑ̃₀, ϑ₀)·η̃ ⊗ η)]]
  + ½ E[∂_y∂_μ f(P_{ϑ₀}, ϑ₀)·η ⊗ η] + R` with `|R| ≤ C E[|η|³ ∧ |η|²]` (2.5)–(2.6).
`E Ẽ` is the iterated integral over `P ⊗ P` (`ω` untilded, `ω'` tilded). -/
theorem lemma_2_1 {Ω : Type*} {F₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {d : ℕ}
    {P : Measure Ω} {B : ℝ≥0 → Ω → Fin d → ℝ} {T : ℝ≥0} (hS : IsSetting F₀ P B T)
    (f : Measure (E d) → ℝ) (Dμf : Measure (E d) → E d → E d)
    (Dμμf : Measure (E d) → E d → Fin d → E d → E d) (DyDμf : Measure (E d) → E d → Fin d → E d)
    (hf : IsC21bP2With P f Dμf Dμμf DyDμf) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ϑ₀ ϑ : Ω → E d, MemLp ϑ₀ 2 P → MemLp ϑ 2 P →
      |f (P.map ϑ) - f (P.map ϑ₀)
          - ∫ ω, inner ℝ (Dμf (P.map ϑ₀) (ϑ₀ ω)) (ϑ ω - ϑ₀ ω) ∂P
          - (1 / 2) * ∫ ω, ∫ ω', ∑ i, ∑ j,
              Dμμf (P.map ϑ₀) (ϑ₀ ω) j (ϑ₀ ω') i * (ϑ ω' i - ϑ₀ ω' i) * (ϑ ω j - ϑ₀ ω j) ∂P ∂P
          - (1 / 2) * ∫ ω, ∑ i, ∑ j,
              DyDμf (P.map ϑ₀) (ϑ₀ ω) j i * (ϑ ω i - ϑ₀ ω i) * (ϑ ω j - ϑ₀ ω j) ∂P|
        ≤ C * ∫ ω, min (‖ϑ ω - ϑ₀ ω‖ ^ 3) (‖ϑ ω - ϑ₀ ω‖ ^ 2) ∂P := by sorry

end MeanFieldPDE.Classical
