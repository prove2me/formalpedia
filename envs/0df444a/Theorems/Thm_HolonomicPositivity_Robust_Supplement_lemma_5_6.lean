-- Prove2me | Theorems.Thm_HolonomicPositivity_Robust_Supplement_lemma_5_6
-- name    : HolonomicPositivity.Robust.Supplement.lemma_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:55:50.325839+00:00
-- url     : https://prove2.me/theorems/4b3331a3-9342-433a-813b-7257c3242af2
-- title:
--   Lemma 5.6 — nonpositive combinations of oscillating products
-- statement:
--   Let $\alpha\in\mathbb R\setminus\{0\}$, $-1<\beta<1/2$, and $\gamma,\delta\in\mathbb R$. Define $g,h$ by (16), namely
--   $$g(n)=\prod_{k=1}^n\left(\frac12+\frac{1+i\alpha}{4k}\right),\qquad h(n)=\prod_{k=1}^n\left(\beta+\frac\gamma k+\frac{\gamma+\delta}{k^2}\right).$$
--   For $(s,t,u)\in\mathbb R^3$, let $F_{s,t,u}=s(g+\bar g)+ti(g-\bar g)+uh$, a real sequence. Then
--   $$\forall(s,t,u),\quad F_{s,t,u}\text{ is not robustly ultimately positive in its coefficients}.$$
--   Moreover, if $\beta+\gamma/x+\delta/x^2\le0$ eventually, then
--   $$\forall(s,t,u),\quad F_{s,t,u}\text{ is not ultimately positive}.$$
--   Coefficient robustness means that some open neighborhood of $(s,t,u)$ consists entirely of ultimately positive combinations. The product uses $\gamma+\delta$ while the additional inequality uses $\delta$, as in the source.
--
--   The two clauses support the counterexample constructions in Theorem 3.5 and Lemma 5.7.
--
--   Differences from the source:
--   - encoding: three real coefficients and the real-valued sequences g+conj(g), i(g-conj(g)), h → Fin 3 → ℝ coefficients, real parts of the two complex expressions, coordinate open balls; reason: the complex expressions are real; their real parts preserve values, and coordinate balls give the same neighborhoods of coefficients
-- source:
--   Fugen Hagihara, Positivity Proofs for Third-Order Holonomic Sequences via Differences Scaled by Rational Functions, STOC 2027 submission #328 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/328.pdf, SHA-256 b828a1da95302dcc4eef96a5cd5df68531d46030b0db425e11667ab782afead2; Lemma 5.6, PDF p.15 (printed 15); global assumptions PDF pp.1-2, real eventual comparisons PDF pp.4-5; proof §5.1.1-5.1.3 or §5.2 as applicable.

import Mathlib
import Definitions.Def_HolonomicPositivity_Robust_Supplement_Products

namespace HolonomicPositivity.Robust.Supplement

/-- Lemma 5.6, Fugen Hagihara, STOC 2027 submission #328 (October 2026), PDF p.15,
printed XX:15. Both clauses, with robustness in combination coefficients and strict positivity. -/
theorem lemma_5_6 (α β γ δ : ℝ) (hα : α ≠ 0) (hβlo : -1 < β) (hβhi : β < 1 / 2) :
    (∀ v : Fin 3 → ℝ, ¬ RobustCombination α β γ δ v) ∧
      (EventuallyGE (fun _ => 0) (fun x => β + γ / x + δ / x ^ 2) →
        ∀ v : Fin 3 → ℝ, ¬ UltimatelyPositive (combination α β γ δ v)) := by sorry

end HolonomicPositivity.Robust.Supplement
