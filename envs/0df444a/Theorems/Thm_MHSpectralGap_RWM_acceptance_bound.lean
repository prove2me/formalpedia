-- Prove2me | Theorems.Thm_MHSpectralGap_RWM_acceptance_bound
-- name    : MHSpectralGap.RWM.acceptance_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T22:15:07.254212+00:00
-- url     : https://prove2.me/theorems/72e376e1-3f11-4a8c-9ba3-f08264b07e86
-- title:
--   Proof of Theorem 2.17, p. 16 — the RWM acceptance probability satisfies α(x) ≤ (1 + 2λδ)^{−m/2} exp(Σ δλ²i²x_i²/(2δλ + 1)) for λ ∈ [0, 1]
-- statement:
--   Consider random walk Metropolis on $\mathbb R^m$ for the Gaussian target $\gamma_m$ of (2.5) (coordinates independent, $x_i\sim\mathcal N(0,1/i^2)$), with step size $\delta>0$: proposal $y=x+\sqrt{2\delta}\,\xi$, $\xi\sim\gamma_m$, and acceptance $\alpha(x,y)=1\wedge\exp\bigl(-\sum_{i=1}^m\frac{i^2}{2}(y_i^2-x_i^2)\bigr)$. Let $\alpha(x)=\int\alpha(x,y)\,Q(x,dy)$ be the expected acceptance probability of a proposal from $x$. Then for every $\lambda\in[0,1]$ and every $x\in\mathbb R^m$,
--
--   $$
--   \alpha(x)\;\le\;(1+2\lambda\delta)^{-m/2}\exp\Bigl(\sum_{i=1}^m\frac{\delta\lambda^2 i^2x_i^2}{2\delta\lambda+1}\Bigr).
--   $$
--
--   For $x$ in a fixed ball of $\mathcal H^\sigma$ and $\lambda,\delta$ decaying as suitable powers of $m$, the first factor decays faster than any power of $m$ while the second stays bounded; this collapse of the acceptance probability is what drives Theorem 2.17 (1).
--
--   **Formalization Note** The range $\lambda\in[0,1]$ is the one where the elementary bound $u\wedge v\le u^\lambda v^{1-\lambda}$ used on the page holds; the paper applies it with $\lambda=m^{-b}\le 1$. Coordinates are indexed by `Fin m`, coordinate $i$ carrying the weight $(i+1)^2$ (the paper's $i=1,\dots,m$). The power $(1+2\lambda\delta)^{-m/2}$ is a real power of a positive base.
-- source:
--   Hairer, Stuart and Vollmer, Spectral gaps for a Metropolis–Hastings algorithm in infinite dimensions, arXiv:1112.1392v4, p. 16, proof of Theorem 2.17, the displays from "Thus we use u ∧ v ≤ u^λ v^{1−λ} to bound" to "≤ (1 + 2λδ)^{−m/2} exp(...)"

import Mathlib
import Definitions.Def_MHSpectralGap_RWM_MHKernel
import Definitions.Def_MHSpectralGap_RWM_L2Gap
import Definitions.Def_MHSpectralGap_RWM_Conductance
import Definitions.Def_MHSpectralGap_RWM_RWMKernel

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MHSpectralGap.RWM

/-- The acceptance bound in the proof of Theorem 2.17, p. 16: for `0 < δ`, `λ ∈ [0, 1]` and
every `x ∈ ℝ^m`,
`α(x) ≤ (1 + 2λδ)^{−m/2} exp(∑_{i=1}^m δλ² i² x_i² / (2δλ + 1))`. -/
theorem acceptance_bound (m : ℕ) (δ : ℝ) (hδ : 0 < δ) (lam : ℝ) (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (x : Fin m → ℝ) :
    accBar (rwmProposal m δ) (rwmAccept m) x ≤
      ENNReal.ofReal ((1 + 2 * lam * δ) ^ (-(m : ℝ) / 2) *
        Real.exp (∑ i : Fin m, δ * lam ^ 2 * ((i : ℝ) + 1) ^ 2 * x i ^ 2 / (2 * δ * lam + 1))) := by sorry

end MHSpectralGap.RWM
