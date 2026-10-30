-- Prove2me | Theorems.Thm_FoundationsRL_DECLower_klDiv_histLaw_eq_of_standardBorel
-- name    : FoundationsRL.DECLower.klDiv_histLaw_eq_of_standardBorel
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:17:48.456651+00:00
-- url     : https://prove2.me/theorems/2cf855a4-498b-4368-ac24-12147ceb8056
-- title:
--   KL divergence between history laws, equality (p. 109; corrected: standard Borel spaces)
-- statement:
--   Let $\Pi$ and $\mathcal O$ be standard Borel spaces, let $p$ be an algorithm, and let $M,\widehat M:\Pi\to\Delta(\mathbb R\times\mathcal O)$ be probability kernels. For every horizon $T$,
--
--   $$
--   D_{\mathrm{KL}}\bigl(\mathbb P^{\widehat M}\,\big\|\,\mathbb P^M\bigr)=\mathbb E^{\widehat M}\left[\sum_{t=1}^T\mathbb E_{\pi_t\sim p_t(\cdot\mid H_{t-1})}D_{\mathrm{KL}}\bigl(\widehat M(\pi_t)\,\big\|\,M(\pi_t)\bigr)\right].
--   $$
--
--   This is the identity displayed on p. 109, on the spaces where it holds: conditionally on $H_{t-1}$ the law of $\pi_t$ does not depend on the model, so the chain rule leaves only the reward–observation terms.
--
--   Differences from the source:
--   - correction: equality for arbitrary measurable $\Pi,\mathcal O$ → equality for standard Borel $\Pi,\mathcal O$; reason: the printed equality is false in general (counterexample in the inequality milestone, with a countable–cocountable observation space)
--   - generalization: $M,\widehat M$ models of the class (rewards in $[0,1]$) → any probability kernels into $\mathbb R\times\mathcal O$; reason: no reward range is used; models are a special case
--   - encoding: rounds $t=1,\dots,T$ → $0$-based indices; KL in $[0,\infty]$; reason: Lean convention; same instances
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, proof of Proposition 28, p. 109 (KL display before (6.39))

import Mathlib
import Definitions.Def_FoundationsRL_DECLower_histLaw
import Definitions.Def_FoundationsRL_DECLower_Algorithm_policyAt

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace FoundationsRL.DECLower

/-- **KL divergence between history laws (p. 109), equality on standard Borel spaces.**
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, proof of Proposition 28, p. 109: "D_KL(P^M̂ ∥ P^M) = E^M̂[Σ_{t=1}^T E_{π_t∼p_t}
D_KL(M̂(π_t) ∥ M(π_t))] … since conditionally on H_{t−1}, the law of π_t does not depend on the model."

If the decision and observation spaces are standard Borel, then for every algorithm, Markov
kernels `M, M̂` and every `T`:
`D_KL(P^M̂ ∥ P^M) = E_{H_T∼P^M̂}[Σ_{t=1}^T E_{π∼p_t(·|H_{t−1})} D_KL(M̂(π) ∥ M(π))]`.

**Formalization Note.** *Correction*: the notes state the equality without restriction on the
spaces; it fails in general (counterexample in `klDiv_histLaw_le`, with a countable–cocountable
observation space). With standard Borel `D` and `O` it holds, and `π ↦ D_KL(M̂(π) ∥ M(π))` is
measurable. No reward range is needed (any Markov kernels). 0-based rounds. -/
theorem klDiv_histLaw_eq_of_standardBorel {D O : Type*} [MeasurableSpace D] [MeasurableSpace O]
    [StandardBorelSpace D] [StandardBorelSpace O]
    (alg : Algorithm D O) (M Mhat : Kernel D (ℝ × O)) [IsMarkovKernel M] [IsMarkovKernel Mhat]
    (T : ℕ) :
    klDiv (histLaw alg Mhat T) (histLaw alg M T)
      = ∫⁻ h, ∑ t : Fin T, ∫⁻ d, klDiv (Mhat d) (M d) ∂(alg.policyAt T t h)
          ∂(histLaw alg Mhat T) := by sorry

end FoundationsRL.DECLower
