-- Prove2me | Theorems.Thm_MeanFieldOpt_FullSupport_lemma_6_5
-- name    : MeanFieldOpt.FullSupport.lemma_6_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T04:10:18.783977+00:00
-- url     : https://prove2.me/theorems/c11a8874-3e42-4240-b821-bcf39854fe9b
-- title:
--   Lemma 6.5 — the SDE (6.3) has a unique strong solution on $[0,1]$
-- statement:
--   Let $\xi$ be a mixture, $f_0$ an admissible terminal condition, $\gamma \in \mathscr L$ and $\Phi = \Phi^\gamma$. Let $(B_t)_{t \ge 0}$ be a standard Brownian motion on a probability space $(\Omega, \mathcal F, \mathbb P)$. Then the stochastic differential equation
--
--   $$
--   dX_t = \xi''(t)\gamma(t)\,\partial_x\Phi(t, X_t)\,dt + \sqrt{\xi''(t)}\,dB_t, \qquad X_0 = 0,
--   $$
--
--   has a strong solution with continuous paths, and it is unique: any two strong solutions $X, Y$ satisfy, almost surely, $X_t = Y_t$ for all $t \in [0,1]$.
--
--   This is the process $X$ in terms of which all the stationarity conditions of the mission are written.
--
--   **Formalization Note** Strong solutions are the published `EthierKurtz.SolvesBrownianSDE` in dimension one, with coefficients extended by $0$ after time $1$ (see the definition `ParisiSDE`). The paper's "almost surely continuous" solution is represented by a solution with continuous paths, which exists after a modification on a null set. The paper's second claim, the stochastic-integral representation (6.7) of $\partial_x\Phi(t,X_t)$, is not part of this item.
-- source:
--   El Alaoui, Montanari, Sellke, Optimization of Mean-field Spin Glasses, arXiv:2001.00904v1, p. 26, Lemma 6.5 (first sentence)

import Mathlib
import Definitions.Def_MeanFieldOpt_FullSupport_IsTerminal
import Definitions.Def_MeanFieldOpt_FullSupport_InL
import Definitions.Def_MeanFieldOpt_FullSupport_ParisiSDE

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MeanFieldOpt.FullSupport

/-- Lemma 6.5, well-posedness part (arXiv:2001.00904v1, p. 26): for `γ ∈ ℒ` and `Φ = Φ^γ`, the SDE
(6.3) driven by a standard Brownian motion has a strong solution on `[0,1]` with continuous paths,
and it is unique: any two strong solutions agree at all times of `[0,1]`, almost surely. -/
theorem lemma_6_5 (ξ : Mixture) (f₀ : ℝ → ℝ) (hf₀ : IsTerminal f₀) (γ : ℝ → ℝ)
    (hγ : InL ξ γ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → EthierKurtz.SDEState 1) (hW : IsBrownianReal (fun t ω => W t ω 0) P) :
    (∃ X : ℝ≥0 → Ω → EthierKurtz.SDEState 1, IsParisiSDESol ξ f₀ γ P W X) ∧
    ∀ X Y : ℝ≥0 → Ω → EthierKurtz.SDEState 1,
      IsParisiSDESol ξ f₀ γ P W X → IsParisiSDESol ξ f₀ γ P W Y →
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ 1 → X t ω = Y t ω := by sorry

end MeanFieldOpt.FullSupport
