-- Prove2me | Theorems.Thm_InvIntegration_Behavioral_lemma_1
-- name    : InvIntegration.Behavioral.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:13:19.270981+00:00
-- url     : https://prove2.me/theorems/c4e74a09-ed7c-4b99-9a72-06147f4d1960
-- title:
--   Lemma 1, EC p. 1 (PDF 33) — a unique fixed point of a continuous f : X × Y → X, X compact, depends continuously on y
-- statement:
--   Let $Y$ be a metric space and $X$ a compact metric space, and let $f: X\times Y\to X$ be continuous. Suppose $\gamma: Y\to X$ satisfies $f(\gamma(y),y)=\gamma(y)$ for every $y$, and that $\gamma(y)$ is the only fixed point of $f(\cdot,y)$: $f(x,y)=x$ implies $x=\gamma(y)$. Then
--   $$\gamma \text{ is continuous.}$$
--
--   The paper uses it to obtain continuity of fill-rate fixed points in the problem data.
--
--   **Formalization Note.** "There exists a unique map $\gamma$ with $f(\gamma(y),y)=\gamma(y)$" is equivalent to: every $f(\cdot,y)$ has exactly one fixed point, $\gamma(y)$; this pointwise form is stated.
-- source:
--   Aflaki & Swinney, Inventory Integration with Rational Consumers, SSRN preprint 2842182 (July 2020), EC p. 1 (PDF 33), Lemma 1

import Mathlib

namespace InvIntegration.Behavioral

theorem lemma_1 {X Y : Type*} [MetricSpace X] [CompactSpace X] [MetricSpace Y]
    (f : X × Y → X) (hf : Continuous f) (γ : Y → X)
    (hγ : ∀ y : Y, f (γ y, y) = γ y) (huniq : ∀ (y : Y) (x : X), f (x, y) = x → x = γ y) :
    Continuous γ := by sorry

end InvIntegration.Behavioral
