-- Prove2me | Theorems.Thm_LiqProvision_Oligopoly_lemma_C_3
-- name    : LiqProvision.Oligopoly.lemma_C_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:40:50.629836+00:00
-- url     : https://prove2.me/theorems/d6383c4d-2e88-4fbe-bd97-817986cbe71f
-- title:
--   Lemma C.3, pp. 32–33 — strict monotonicity of C¹ functions and its stability under small perturbations
-- statement:
--   Let $I=(a,b)$ with $-\infty\le a<b\le\infty$, and let $f:I\to\mathbb R$ be continuously differentiable.
--
--   1. $f$ is increasing on $I$ if and only if $f'\ge0$ on $I$ and $\{x\in I: f'(x)=0\}$ is nowhere dense.
--   2. If $f$ is increasing on $I$, then for every compact $K\subset\{f'>0\}$ and every continuously differentiable $g:I\to\mathbb R$ vanishing outside $K$, there is $\varepsilon'>0$ such that
--   $$f+\varepsilon g\ \text{ is increasing on } I\qquad\text{for all }\varepsilon\in[-\varepsilon',\varepsilon'] .$$
--
--   It justifies the local perturbation argument in the derivation of the ODE (3.8).
--
--   **Formalization Note.** Generic statement. $I$ is a nonempty open order-connected subset of $\mathbb R$, i.e. an open interval with possibly infinite ends. In (b) the page does not state that $f$ is increasing, but its proof uses $\{f'<0\}=\emptyset$ and the nowhere density of $\{f'=0\}$; without it (b) is false (take $f(x)=-x$ and $g=0$). The statement adds that hypothesis.
-- source:
--   Herdegen, Muhle-Karbe and Stebegg, Liquidity Provision with Adverse Selection and Inventory Costs, arXiv:2107.12094v1, pp. 32–33, Lemma C.3

import Mathlib

namespace LiqProvision.Oligopoly
theorem lemma_C_3 (I : Set ℝ) (hIo : IsOpen I) (hIc : I.OrdConnected) (hIne : I.Nonempty)
    (f : ℝ → ℝ) (hf : ContDiffOn ℝ 1 f I) :
    (StrictMonoOn f I ↔
      (∀ x ∈ I, 0 ≤ deriv f x) ∧ IsNowhereDense {x | x ∈ I ∧ deriv f x = 0}) ∧
    (StrictMonoOn f I → ∀ Kc : Set ℝ, IsCompact Kc → Kc ⊆ {x | x ∈ I ∧ 0 < deriv f x} →
      ∀ g : ℝ → ℝ, ContDiffOn ℝ 1 g I → (∀ x ∈ I, x ∉ Kc → g x = 0) →
        ∃ ε' > 0, ∀ ε ∈ Set.Icc (-ε') ε', StrictMonoOn (fun x => f x + ε * g x) I) := by sorry
end LiqProvision.Oligopoly
