-- Prove2me | Theorems.Thm_HolonomicPositivity_Robust_Supplement_lemma_5_7
-- name    : HolonomicPositivity.Robust.Supplement.lemma_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:54:44.127407+00:00
-- url     : https://prove2.me/theorems/05f730c9-e3bf-4c7f-bf19-db398f98ac9b
-- title:
--   Lemma 5.7 — nonexistence arbitrarily below the threshold
-- statement:
--   Let $p_0,p_1,p_2\in\mathbb R$ satisfy, eventually as real $x\to+\infty$,
--   $$p_0+\frac{p_1}{x}+\frac{p_2}{x^2}\ge-\frac14-\frac{1}{16x^2}.$$
--   For every $\varepsilon>0$ there exist rational functions $P,Q$ with no poles on $\mathbb N$ such that
--   $$P(x)=p_0+\frac{p_1}{x}+\frac{p_2}{x^2}+O(x^{-3}),\qquad Q(x)\ge R_P(x)-\frac{\varepsilon}{x^2},$$
--   and the recurrence $f(n+3)=f(n+2)+P(n)f(n+1)+Q(n)f(n)$ has no ultimately positive real solution. Here $R_P$ is the case (II-1) threshold computed from the given $p_0,p_1,p_2$; the displayed inequality for $Q$ is plain eventual order.
--
--   This supplies the nonexistence construction used in the necessity direction of Theorem 3.4. No nonvanishing condition on $Q(n)$ is imposed on the constructed witnesses.
--
--   Differences from the source:
--   - encoding: P,Q in R(x) under the global no-pole convention → RatFunc ℝ witnesses with NoPolesOnNat conclusions and the published comparison predicates; reason: makes the standing convention and the real-variable eventual order explicit without changing any instance
-- source:
--   Fugen Hagihara, Positivity Proofs for Third-Order Holonomic Sequences via Differences Scaled by Rational Functions, STOC 2027 submission #328 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/328.pdf, SHA-256 b828a1da95302dcc4eef96a5cd5df68531d46030b0db425e11667ab782afead2; Lemma 5.7, PDF p.16 (printed 16); global assumptions PDF pp.1-2, real eventual comparisons PDF pp.4-5; proof §5.1.1-5.1.3 or §5.2 as applicable.

import Mathlib
import Definitions.Def_HolonomicPositivity_Robust_Conditions
import Definitions.Def_HolonomicPositivity_Robust_Recurrence

namespace HolonomicPositivity.Robust.Supplement

/-- Lemma 5.7, Fugen Hagihara, STOC 2027 submission #328 (October 2026), PDF p.16,
printed XX:16. Pole-freeness of the constructed coefficients is the global convention on p.1. -/
theorem lemma_5_7 (p₀ p₁ p₂ : ℝ)
    (hp : EventuallyGE (fun x => p₀ + p₁ / x + p₂ / x ^ 2)
      (fun x => -(1 / 4) - 1 / (16 * x ^ 2))) (ε : ℝ) (hε : 0 < ε) :
    ∃ P Q : RatFunc ℝ, NoPolesOnNat P ∧ NoPolesOnNat Q ∧
      EqMod (ev P) (fun x => p₀ + p₁ / x + p₂ / x ^ 2) (-3) ∧
      EventuallyGE (ev Q) (fun x => thresholdOne p₀ p₁ p₂ x - ε / x ^ 2) ∧
      ¬ ∃ f : ℕ → ℝ, IsSolution P Q f ∧ UltimatelyPositive f := by sorry

end HolonomicPositivity.Robust.Supplement
