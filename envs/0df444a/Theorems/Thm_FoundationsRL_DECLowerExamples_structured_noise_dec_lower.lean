-- Prove2me | Theorems.Thm_FoundationsRL_DECLowerExamples_structured_noise_dec_lower
-- name    : FoundationsRL.DECLowerExamples.structured_noise_dec_lower
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:23:01.837105+00:00
-- url     : https://prove2.me/theorems/34afbb7f-1628-496e-a2ad-78f0ef83cff9
-- title:
--   Example 6.5 (cont'd) — structured noise gives $\mathrm{dec}^{\mathrm c}_\varepsilon(\mathcal M_{\mathrm{MAB\text{-}SN}})\ge\frac18\mathbb I\{\varepsilon\ge\sqrt{2/A}\}$ (corrected: $A\ge2$)
-- statement:
--   Let $\mathcal M_{\mathrm{MAB\text{-}SN}}=\{M_1,\dots,M_A\}\cup\{\widehat M\}$ be the class of bandits with structured noise with $A\ge2$ actions: $M_i(\pi)=\mathcal N(1/2,1)$ for $\pi\ne i$, $M_i(i)=\mathrm{Ber}(3/4)$, and $\widehat M(\pi)=\mathcal N(1/2,1)$. Then for every $\varepsilon$,
--   $$
--   \mathrm{dec}^{\mathrm c}_\varepsilon(\mathcal M_{\mathrm{MAB\text{-}SN}})\ \ge\ \frac18\cdot\mathbb I\Bigl\{\varepsilon\ge\sqrt{2/A}\Bigr\}.
--   $$
--
--   The family $\{M_1,\dots,M_A\}$ with reference $\widehat M$ satisfies the conditions of Proposition 30 with $\alpha=1/4$ and $\beta^2=2$ (a Gaussian and a Bernoulli law are mutually singular). With Proposition 28 this gives a regret lower bound of order $A$, matching the upper bound of order $A\cdot\mathrm{Est}_{\mathrm H}$.
--
--   **Formalization Note** $\mathrm{dec}^{\mathrm c}_\varepsilon(\mathcal M)$ is the class coefficient $\sup_{\widehat M\in\mathrm{co}(\mathcal M)}\mathrm{dec}^{\mathrm c}_\varepsilon(\mathcal M\cup\{\widehat M\},\widehat M)$, with values in $[0,\infty]$.
--
--   Differences from the source:
--   - correction: any number A of actions → 2 ≤ A; reason: for A = 1 there is a single decision, every model in the convex hull has gap 0, so the coefficient is 0 while I{ε ≥ √2} = 1 for ε ≥ √2
--   - generalization: dec^c_ε(M_MAB-SN) ≳ I{ε ≥ √(2/A)} → dec^c_ε(M_MAB-SN) ≥ (1/8)·I{ε ≥ √(2/A)}; reason: the explicit absolute constant 1/8 = α/2 of Proposition 30 implies the bound up to an absolute constant
--   - reading: M = {M₁, …, M_A} (as recalled on p. 111) → M_MAB-SN = {M₁, …, M_A} ∪ {M̂}; reason: the symbol M_MAB-SN is defined on p. 99 with M̂ included, and the example sets M̂(π) = N(1/2, 1) as the reference model of Proposition 30
--   - encoding: real-valued coefficient → values in [0, ∞]; reason: the coefficient is [0, ∞]-valued; same instances
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Example 6.5 (cont'd), p. 111

import Mathlib
import Definitions.Def_FoundationsRL_DECLowerExamples_constrainedDEC
import Definitions.Def_FoundationsRL_DECLowerExamples_structuredNoiseClass

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace FoundationsRL.DECLowerExamples

/-- **Example 6.5 (cont'd): bandits with structured noise have `dec^c_ε(M_MAB-SN) ≳ I{ε ≥ √(2/A)}`.**
With `M̂(π) = N(1/2, 1)` the family `{M_1, …, M_A}` meets the conditions of Proposition 30 with
`α = 1/4` and `β² = 2`, so `dec^c_ε(M_MAB-SN) ≥ (1/8) · I{ε ≥ √(2/A)}` for `A ≥ 2`.
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, Example 6.5 (cont'd), p. 111 (corrected: `A ≥ 2`).

**Formalization Note.** `≳` is stated with the explicit constant `1/8 = α/2` that Proposition 30's
argument gives. `dec^c_ε(M)` is the class coefficient `sup_{M̂ ∈ co(M)} dec^c_ε(M ∪ {M̂}, M̂)`.
For `A = 1` the statement is false (one decision, every gap is `0`), hence `2 ≤ A`. -/
theorem structured_noise_dec_lower (A : ℕ) (hA : 2 ≤ A) (ε : ℝ) :
    (if Real.sqrt (2 / A) ≤ ε then (1 / 8 : ℝ≥0∞) else 0) ≤
      constrainedDEC ε (structuredNoiseClass A) := by sorry

end FoundationsRL.DECLowerExamples
