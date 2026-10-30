-- Prove2me | Theorems.Thm_FoundationsRL_DECLower_klDiv_histLaw_le
-- name    : FoundationsRL.DECLower.klDiv_histLaw_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:17:23.886806+00:00
-- url     : https://prove2.me/theorems/eb25b723-926f-4e5e-9c56-eeca24f0f670
-- title:
--   KL divergence between history laws, $\le$ (p. 109; corrected: "=" fails on general spaces)
-- statement:
--   Let $\Pi$ and $\mathcal O$ be measurable spaces, let $p$ be an algorithm, and let $M,\widehat M:\Pi\to\Delta(\mathbb R\times\mathcal O)$ be probability kernels such that $\pi\mapsto D_{\mathrm{KL}}(\widehat M(\pi)\,\|\,M(\pi))$ is measurable. For every horizon $T$, the laws $\mathbb P^{\widehat M},\mathbb P^M$ of the history $H_T$ satisfy
--
--   $$
--   D_{\mathrm{KL}}\bigl(\mathbb P^{\widehat M}\,\big\|\,\mathbb P^M\bigr)\le\mathbb E^{\widehat M}\left[\sum_{t=1}^T\mathbb E_{\pi_t\sim p_t(\cdot\mid H_{t-1})}D_{\mathrm{KL}}\bigl(\widehat M(\pi_t)\,\big\|\,M(\pi_t)\bigr)\right].
--   $$
--
--   The decisions are drawn by the same algorithm under both models, so only the reward–observation kernels contribute. This is the step of the proof of Proposition 28 that bounds the statistical distance between the two interaction histories by the per-round information gain.
--
--   Differences from the source:
--   - correction: $D_{\mathrm{KL}}(\mathbb P^{\widehat M}\|\mathbb P^M)=\mathbb E^{\widehat M}[\sum_t\mathbb E_{\pi_t\sim p_t}D_{\mathrm{KL}}(\widehat M(\pi_t)\|M(\pi_t))]$ → $\le$; reason: the equality is false for general measurable spaces: $T=1$, $\Pi=[0,1]$ Borel, $p_1$ Lebesgue, $\mathcal O=[0,1]$ countable–cocountable, $\widehat M(\pi)=\delta_0\otimes\delta_\pi$, $M(\pi)=\delta_0\otimes\nu$ ($\nu(B)=1$ iff $B$ cocountable); the two history laws coincide while every $D_{\mathrm{KL}}(\widehat M(\pi)\|M(\pi))=+\infty$
--   - reading: $\mathbb E_{\pi_t\sim p_t}D_{\mathrm{KL}}(\widehat M(\pi_t)\|M(\pi_t))$ → a Lebesgue integral with $\pi\mapsto D_{\mathrm{KL}}(\widehat M(\pi)\|M(\pi))$ assumed measurable; reason: the expectation presupposes measurability
--   - generalization: $M,\widehat M$ models of the class (rewards in $[0,1]$) → any probability kernels into $\mathbb R\times\mathcal O$; reason: the argument uses no reward range; models are a special case
--   - encoding: rounds $t=1,\dots,T$ and histories $H_{t-1}$ → $0$-based indices; KL in $[0,\infty]$; reason: Lean convention; same instances
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, proof of Proposition 28, p. 109 (KL display before (6.39))

import Mathlib
import Definitions.Def_FoundationsRL_DECLower_histLaw
import Definitions.Def_FoundationsRL_DECLower_Algorithm_policyAt

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace FoundationsRL.DECLower

/-- **KL divergence between history laws (p. 109), inequality form.**
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, proof of Proposition 28, p. 109: "Using the chain rule for KL divergence, we have
D_KL(P^M̂ ∥ P^M) = E^M̂[Σ_{t=1}^T E_{π_t∼p_t} D_KL(M̂(π_t) ∥ M(π_t))]".

For every algorithm, Markov kernels `M, M̂ : D → Δ(ℝ × O)` with `π ↦ D_KL(M̂(π) ∥ M(π))`
measurable, and every `T`:
`D_KL(P^M̂ ∥ P^M) ≤ E_{H_T∼P^M̂}[Σ_{t=1}^T E_{π∼p_t(·|H_{t−1})} D_KL(M̂(π) ∥ M(π))]`.

**Formalization Note.** *Correction*: the notes print "="; in the DMSO generality (arbitrary
measurable decision and observation spaces) it fails: `T = 1`, `D = [0,1]` Borel, `p_1` Lebesgue,
`O = [0,1]` countable–cocountable, `M̂(d) = δ_0 ⊗ δ_d`, `M(d) = δ_0 ⊗ ν` (`ν` the 0–1 measure of
cocountable sets): both history laws coincide, while every `D_KL(M̂(d) ∥ M(d)) = ∞`. The proof
of Proposition 28 uses only "≤". The equality on standard Borel spaces is
`klDiv_histLaw_eq_of_standardBorel`. The measurability hypothesis is presupposed by
`E_{π_t∼p_t} D_KL(…)`. No reward range is needed (any Markov kernels). 0-based rounds. -/
theorem klDiv_histLaw_le {D O : Type*} [MeasurableSpace D] [MeasurableSpace O]
    (alg : Algorithm D O) (M Mhat : Kernel D (ℝ × O)) [IsMarkovKernel M] [IsMarkovKernel Mhat]
    (hmeas : Measurable (fun d => klDiv (Mhat d) (M d))) (T : ℕ) :
    klDiv (histLaw alg Mhat T) (histLaw alg M T)
      ≤ ∫⁻ h, ∑ t : Fin T, ∫⁻ d, klDiv (Mhat d) (M d) ∂(alg.policyAt T t h)
          ∂(histLaw alg Mhat T) := by sorry

end FoundationsRL.DECLower
