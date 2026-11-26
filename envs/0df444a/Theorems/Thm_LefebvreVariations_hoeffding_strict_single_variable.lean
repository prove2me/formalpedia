-- Prove2me | Theorems.Thm_LefebvreVariations_hoeffding_strict_single_variable
-- name    : LefebvreVariations.hoeffding_strict_single_variable
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:27:39.029045+00:00
-- url     : https://prove2.me/theorems/e29f56be-c100-511f-8a7a-565c9b479d2b
-- title:
--   Lefebvre's variations, No. 169 — on a theme by Lugosi and Mehrabian: Hoeffding's strict two-sided inequality for a single variable bounded in [0,b]
-- statement:
--   Let $X$ be a random variable with $0\le X\le b$ for some $b>0$. Then for every $t\ge0$,
--   $$\mathbb{P}\bigl(|X-\mathbb{E}X|>t\bigr)<2\exp\!\Bigl(-\frac{2t^2}{b^2}\Bigr).$$
--
--   This is Hoeffding's inequality in its strict two-sided form for a single bounded variable (sample size $n=1$).
--
--   **Formalization Note** The statement is that of `MultiplayerNoCollision.proposition_4a` with the hypothesis `n = 1` added. `X : Fin n → Ω → ℝ` is a family of measurable functions with `0 ≤ X k ω ≤ b` at every outcome, `iIndepFun X P` (automatic for one variable), `P.real` is the real-valued probability, and the empirical mean is `(∑ k, X k ω) / n`. The inequality is strict, as printed in the parent.
--
--   **Why this is a variation.** Variation of the open platform problem MultiplayerNoCollision.proposition_4a (strict Hoeffding inequality for the mean of n independent variables in [0,b]). It is the case n=1 in the parent's own statement, so a consequence of the parent. The Proved platform theorem Concentration.hoeffding_two_sided gives the non-strict version (P(|X-EX| >= t) <= 2exp(-2t^2/b^2)) but not the strict inequality asked for here.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Parent: MultiplayerNoCollision.proposition_4a (platform, Open), Proposition 4(a) of Lugosi and Mehrabian, Multiplayer bandits without observing collision information, arXiv:1808.08416v2, p.9, as given in the parent's source field (not re-checked), citing a Hoeffding inequality [20, Thm 2.3]. Original: W. Hoeffding, Probability inequalities for sums of bounded random variables, J. Amer. Statist. Assoc. 58 (1963) 13-30 (reference verified online; theorem number not checked, cited from memory). Numerical check in python3 over 200000 random discrete distributions on [0,1] (b=1) at all critical thresholds t and t+-1e-9: the minimum of 2exp(-2t^2) - P(|X-EX|>t) was 0.2134 > 0. Strictness holds because Markov's inequality is strict for t>0 and the bound at t=0 is 2>=1+.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

open MeasureTheory ProbabilityTheory

/-- The case `n = 1` of `MultiplayerNoCollision.proposition_4a` (Hoeffding's inequality, strict form): a random variable
`X` with `0 ≤ X ≤ b` satisfies `P(|X - E X| > t) < 2 exp(-2t²/b²)` for every `t ≥ 0`.
Source: W. Hoeffding, J. Amer. Statist. Assoc. 58 (1963), Thm 2 (cited from memory). The strict form is the one printed in Lugosi–Mehrabian, arXiv:1808.08416v2, Prop. 4(a). -/
theorem hoeffding_strict_single_variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 1 ≤ n) (hn1 : n = 1) (X : Fin n → Ω → ℝ) (hX_meas : ∀ k, Measurable (X k))
    (hX_indep : iIndepFun X P) (b : ℝ) (hb : 0 < b) (hX : ∀ k ω, 0 ≤ X k ω ∧ X k ω ≤ b)
    (t : ℝ) (ht : 0 ≤ t) :
    P.real {ω | t < |(∑ k, X k ω) / n - ∫ ω', (∑ k, X k ω') / n ∂P|} <
      2 * Real.exp (-2 * n * t ^ 2 / b ^ 2) := by
  sorry

end LefebvreVariations
