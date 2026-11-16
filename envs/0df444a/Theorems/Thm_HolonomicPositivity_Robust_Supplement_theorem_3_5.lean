-- Prove2me | Theorems.Thm_HolonomicPositivity_Robust_Supplement_theorem_3_5
-- name    : HolonomicPositivity.Robust.Supplement.theorem_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:56:25.496865+00:00
-- url     : https://prove2.me/theorems/ba28c30e-5f0c-4e0e-b81c-65017efb187e
-- title:
--   Theorem 3.5 — sharpness throughout case (II-1)
-- statement:
--   For every $\varepsilon>0$, every real $p_0>-1/3$, and every $p_1,p_2\in\mathbb R$, there are rational functions $P,Q$ with no poles on $\mathbb N$ such that
--   $$P(x)=p_0+\frac{p_1}{x}+\frac{p_2}{x^2}+O(x^{-3}),\qquad Q(x)\ge R_P(x)-\frac{\varepsilon}{x^2},$$
--   yet the normalized third-order recurrence admits no robustly ultimately positive solution. Here $R_P$ is the case (II-1) threshold computed from $p_0,p_1,p_2$; the comparison for $Q$ is plain eventual order as real $x\to+\infty$.
--
--   This companion theorem shows that the sufficient boundary can be approached from below without robust ultimate positivity, throughout the full range $p_0>-1/3$. It does not impose nonvanishing of the constructed $Q$ on natural indices.
--
--   Differences from the source:
--   - encoding: P,Q in R(x) under the global no-pole convention → RatFunc ℝ witnesses with NoPolesOnNat conclusions and the published comparison predicates; reason: makes the standing convention and the real-variable eventual order explicit without changing any instance
-- source:
--   Fugen Hagihara, Positivity Proofs for Third-Order Holonomic Sequences via Differences Scaled by Rational Functions, STOC 2027 submission #328 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/328.pdf, SHA-256 b828a1da95302dcc4eef96a5cd5df68531d46030b0db425e11667ab782afead2; Theorem 3.5, PDF p.6 (printed 6); global assumptions PDF pp.1-2, real eventual comparisons PDF pp.4-5; proof §5.1.1-5.1.3 or §5.2 as applicable.

import Mathlib
import Definitions.Def_HolonomicPositivity_Robust_Conditions
import Definitions.Def_HolonomicPositivity_Robust_Recurrence

namespace HolonomicPositivity.Robust.Supplement

/-- Theorem 3.5, Fugen Hagihara, STOC 2027 submission #328 (October 2026), PDF p.6,
printed XX:6. Every p₀>-1/3 and every positive ε; witnesses, including pole-freeness, are conclusions. -/
theorem theorem_3_5 (ε : ℝ) (hε : 0 < ε) (p₀ : ℝ) (hp₀ : -(1 / 3) < p₀)
    (p₁ p₂ : ℝ) :
    ∃ P Q : RatFunc ℝ, NoPolesOnNat P ∧ NoPolesOnNat Q ∧
      EqMod (ev P) (fun x => p₀ + p₁ / x + p₂ / x ^ 2) (-3) ∧
      EventuallyGE (ev Q) (fun x => thresholdOne p₀ p₁ p₂ x - ε / x ^ 2) ∧
      ¬ AdmitsRobustlyUltimatelyPositiveSolution P Q := by sorry

end HolonomicPositivity.Robust.Supplement
