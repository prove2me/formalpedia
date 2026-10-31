-- Prove2me | Theorems.Thm_FoundationsRL_DECExamples_igw_cover_value_bound
-- name    : FoundationsRL.DECExamples.igw_cover_value_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:21:38.80044+00:00
-- url     : https://prove2.me/theorems/e8cc6d3e-e2d9-4a3a-b9e3-ac68692548c2
-- title:
--   Proof of Proposition 18, last display — the value is at most $\varepsilon+\varepsilon^{-d}/\gamma$
-- statement:
--   Let $(\Pi,\rho)$ be a nonempty metric space with $\mathcal N_\rho(\Pi,\varepsilon)\le\varepsilon^{-d}$ for all $\varepsilon\in(0,1]$, where $d>0$. Let $\widehat f:\Pi\to[0,1]$, $\gamma\ge1$ and $\varepsilon\in(0,1]$. Let $\Pi'$ witness the covering number $\mathcal N_\rho(\Pi,\varepsilon)$ and let $p$ be inverse gap weighting with parameter $\gamma$ applied to $\widehat f$, restricted to $\Pi'$. Then $|\Pi'|\le\varepsilon^{-d}$, and for every $1$-Lipschitz $f:\Pi\to[0,1]$,
--
--   $$
--   \mathbb E_{\pi\sim p}\Big[f(\pi_f)-f(\pi)-\gamma\cdot\big(f(\pi)-\widehat f(\pi)\big)^2\Big]\le\varepsilon+\frac{\varepsilon^{-d}}{\gamma}.
--   $$
--
--   This is the value of the strategy before $\varepsilon$ is tuned; the choice $\varepsilon=\gamma^{-1/(d+1)}$ balances the two terms.
--
--   **Formalization Note** $f(\pi_f)$ is $\sup_{\pi}f(\pi)$. Distributions are `PMF`.
--
--   Differences from the source:
--   - generalization: hypothesis N_ρ(Π, ε) ≤ ε^{−d} for all ε > 0, and ε > 0 → hypothesis on ε ∈ (0, 1], and ε ∈ (0, 1]; reason: the printed hypothesis fails at every ε > 1 on a nonempty space (N_ρ ≥ 1 > ε^{−d}), so as printed the display has no instance; the Lean hypothesis is implied by the printed one, and at ε > 1 the display's |Π′| ≤ ε^{−d} < 1 is false on every nonempty space
--   - encoding: f(π_f) → sup over Π of f; reason: π_f need not exist on a non-compact space; equal when it exists
--   - encoding: a metric space Π → a nonempty metric space; reason: on the empty space there are no distributions and the value is undefined
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, proof of Proposition 18, last display, p. 74

import Mathlib
import Definitions.Def_FoundationsRL_DECExamples_offsetValue
import Definitions.Def_FoundationsRL_DECExamples_lipschitzClass
import Definitions.Def_FoundationsRL_DECExamples_HasCoveringGrowth
import Definitions.Def_FoundationsRL_DECExamples_IsCoverWitness
import Definitions.Def_FoundationsRL_DECExamples_IsIGWOn
open scoped NNReal

namespace FoundationsRL.DECExamples

/-- **Proof of Proposition 18, last display: the value before optimizing `ε`.** From the growth of
`N_ρ(D, ε)`, `|D'| ≤ ε^{−d}`, so for every `f` in the class the value of the inverse gap weighting
strategy is at most `ε + ε^{−d} / γ`.
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, proof of Proposition 18, p. 74.

**Formalization Note.** `ε ∈ (0, 1]`, the range on which `HasCoveringGrowth` holds. `f(π_f)` is
`⨆ π, f π`, inside `offsetValue`. -/
theorem igw_cover_value_bound {D : Type*} [MetricSpace D] [Nonempty D] (d : ℝ) (hd : 0 < d)
    (hgrowth : HasCoveringGrowth D d) (fhat : D → ℝ) (hfhat : ∀ π, fhat π ∈ Set.Icc (0 : ℝ) 1)
    (γ : ℝ) (hγ : 1 ≤ γ) (ε : ℝ≥0) (hε : 0 < ε) (hε' : ε ≤ 1) (D' : Finset D)
    (hD' : IsCoverWitness ε D') (p : PMF D) (hp : IsIGWOn D' fhat γ p) :
    (D'.card : ℝ) ≤ (ε : ℝ) ^ (-d) ∧
    ∀ f ∈ lipschitzClass D, offsetValue p f fhat γ ≤ ε + (ε : ℝ) ^ (-d) / γ := by sorry

end FoundationsRL.DECExamples
