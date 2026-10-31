-- Prove2me | Theorems.Thm_FoundationsRL_DECLowerExamples_gaussian_bandit_dec_lower
-- name    : FoundationsRL.DECLowerExamples.gaussian_bandit_dec_lower
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:22:02.497496+00:00
-- url     : https://prove2.me/theorems/29aac33a-7141-43ef-9f0b-371f308487f8
-- title:
--   Example 6.4 (cont'd) — the Gaussian bandit has $\mathrm{dec}^{\mathrm c}_\varepsilon(\mathcal M,\widehat M)\ge\varepsilon\sqrt{A/2}$ (corrected: $A\ge2$, $\varepsilon\sqrt{2A}\le1/2$)
-- statement:
--   Let $\mathcal M=\mathcal M_{\mathrm{MAB\text{-}G}}$ be the Gaussian bandit class with $A\ge 2$ actions and $\widehat M(\pi)=\mathcal N(1/2,1)$ for every $\pi$. If $\varepsilon\sqrt{2A}\le 1/2$, then
--   $$
--   \mathrm{dec}^{\mathrm c}_\varepsilon(\mathcal M,\widehat M)\ \ge\ \varepsilon\sqrt{A/2}.
--   $$
--
--   Combined with the regret lower bound of Proposition 28, this gives the $\widetilde\Omega(\sqrt{AT})$ lower bound for Gaussian multi-armed bandits.
--
--   **Formalization Note** Actions are `Fin A`; the coefficient takes values in $[0,\infty]$ and the left-hand side is `ENNReal.ofReal`, so the statement is trivial for $\varepsilon\le0$.
--
--   Differences from the source:
--   - correction: any number A of actions → 2 ≤ A; reason: the step 1 − p(i) ≥ 1/2 needs p(i) ≤ 1/A ≤ 1/2; for A = 1 there is a single decision, every gap is 0 and the coefficient is 0 < ε√(1/2) for every ε > 0
--   - correction: any ε > 0 → ε√(2A) ≤ 1/2; reason: the argument takes Δ = ε√(2A), and the models with mean 1/2 + Δ lie in the class only if Δ ≤ 1/2; without it the display is false: means lie in [0, 1], so the coefficient is at most 1, while ε√(A/2) > 1 for ε > √(2/A)
--   - encoding: real values → values in [0, ∞]; reason: the coefficient is [0, ∞]-valued; for ε > 0 both sides are the source's
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Example 6.4 (cont'd), p. 111, first display

import Mathlib
import Definitions.Def_FoundationsRL_DECLowerExamples_constrainedDECRef
import Definitions.Def_FoundationsRL_DECLowerExamples_gaussianBanditClass

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace FoundationsRL.DECLowerExamples

/-- **Example 6.4 (cont'd): the Gaussian bandit has `dec^c_ε(M, M̂) ≥ ε√(A/2)`.** For
`M = M_MAB-G` with `A ≥ 2` actions and `M̂(π) = N(1/2, 1)`, choosing `Δ = ε√(2A)` gives
`dec^c_ε(M, M̂) ≥ (1 − p(i))Δ ≥ ε√(A/2)`, provided `Δ = ε√(2A) ≤ 1/2`.
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, Example 6.4 (cont'd), p. 111 (corrected: `A ≥ 2`, `ε√(2A) ≤ 1/2`).

**Formalization Note.** The two side conditions are what the argument uses: `1 − p(i) ≥ 1/2`
needs `A ≥ 2`, and the models `M_i` with mean `1/2 + Δ` belong to `M_MAB-G` only if `Δ ≤ 1/2`.
Without them the display is false (for `A = 1` the coefficient is `0`; for large `ε` it is at most
`1` since means lie in `[0, 1]`). `M̂` is the constant kernel `π ↦ N(1/2, 1) ⊗ δ_∅`. -/
theorem gaussian_bandit_dec_lower (A : ℕ) (hA : 2 ≤ A) (ε : ℝ)
    (hε : ε * Real.sqrt (2 * A) ≤ 1 / 2) :
    ENNReal.ofReal (ε * Real.sqrt (A / 2)) ≤
      constrainedDECRef ε (gaussianBanditClass A)
        (Kernel.const (Fin A) ((gaussianReal (1 / 2) 1).map (fun r => (r, ())))) := by sorry

end FoundationsRL.DECLowerExamples
