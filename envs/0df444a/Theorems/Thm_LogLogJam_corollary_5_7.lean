-- Prove2me | Theorems.Thm_LogLogJam_corollary_5_7
-- name    : LogLogJam.corollary_5_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:27:38.605904+00:00
-- url     : https://prove2.me/theorems/a03ccdd4-0043-4cfa-819d-240e74bffd6a
-- title:
--   Corollary 5.7 — $\bar J_t=\bar J_{t-1}+\mathbb E_{\theta,H_{t-1}}[J_{M_t}(\theta)]$
-- statement:
--   For every $T$-adaptive protocol with randomized Gaussian measurements on the squeezed family ($\lambda>1$) and every $1\le t\le T$,
--
--   $$
--   \bar J_t=\bar J_{t-1}+\mathbb E_{\theta,H_{t-1}}\big[J_{M_t}(\theta)\big],
--   $$
--
--   where $M_t$ is the (randomized) measurement chosen at $H_{t-1}$ and $J_{M_t}(\theta)$ is the average of $J_W(\theta)$ over its seed $W$. The Fisher information of the whole protocol is the sum of the information of its rounds.
--
--   Differences from the source:
--
--   - encoding: index $t$ with $1\le t\le T$ → index $t+1$ with $t+1\le T$; reason: a shift of the index
--   - encoding: $J_{M_t}(\theta)$ for a randomized measurement → $\int J_W(\theta)\,d(\text{seed law at }H_{t-1})(W)$; reason: the Fisher information of the pair (seed, outcome) is the seed-average of $J_W$, because the seed law does not depend on $\theta$
--   - encoding: a Gaussian measurement with seed $W\in\mathrm{Cov}_k$ applied to the quantum state $\rho_\theta^{\otimes k}$ → its classical outcome law, the density $f^W_\theta(y)=\exp(-y^\top D^{-1}y)/(\pi^k\sqrt{\det D})$ with $D=V_\theta\otimes I_k+W$; reason: §4.2 (p.17) defines a Gaussian measurement by this outcome law on Gaussian states, and every measurement in the statement is applied to copies of $\rho_\theta$; same instances
--   - generalization: Definition 4.4: the measurement map gives, at each history, a randomized Gaussian measurement on a number $k$ of copies fixed by the history → a Markov kernel from histories to pairs $(k,W)$, so $k$ may also be random given the history; the drawn seed is recorded in the observation; reason: Definition 4.4's protocols are the kernels whose $k$-marginal is a Dirac mass; continuous ensembles are allowed by p.17
--   - encoding: the protocol's maps (no regularity stated) → the seed kernels and the output map are measurable, and seeds lie in $\mathrm{Cov}_k$ almost surely; reason: without measurability the success probability is undefined; this excludes only undefined cases
--   - encoding: $J_W(\theta)=\mathbb E_{Y\sim f^W_\theta}[(\partial_\theta\log f^W_\theta(Y))^2]$ → `measFisher`, the Lebesgue integral $\int f^W_\theta(y)(\partial_\theta\log f^W_\theta(y))^2\,dy\in[0,\infty]$; reason: the same integral; not the closed form $\tfrac12\mathrm{tr}((D^{-1}\partial_\theta D)^2)$ quoted in the proof of Lemma 6.1
--   - encoding: $\theta\in\mathbb T=\mathbb R/\pi\mathbb Z$, uniform law and integrals on $\mathbb T$ → $\theta\in\mathbb R$ with $\pi$-periodic objects; uniform law and integrals over $[0,\pi)$; reason: $V_{\lambda,\theta}$ is $\pi$-periodic, so $[0,\pi)$ is one period; same instances
--   - encoding: probabilities, expectations and Fisher informations as real numbers → values in $[0,\infty]$ (lower Lebesgue integrals of nonnegative functions); reason: every quantity is a nonnegative integral; the extended value avoids junk zeros for non-integrable integrands and agrees with the real value when finite
--   - encoding: energy $E>1/2$ and $\lambda>1$ the solution of $E=\tfrac14(\lambda+\lambda^{-1})$ → $\lambda>1$ as the parameter, $E=\mathrm{energy}\,\lambda=(\lambda+\lambda^{-1})/4$; reason: $\lambda\mapsto(\lambda+\lambda^{-1})/4$ is a bijection from $(1,\infty)$ onto $(1/2,\infty)$; same instances
-- source:
--   Chen, Gong, Ye, Zhang, The log log jam in Gaussian state tomography, arXiv:2607.12983 (version of November 3, 2026, sha256 97b751ca…), Corollary 5.7, p.25 (PDF p.28)

import Mathlib
import Definitions.Def_LogLogJam_GaussProtocol

open MeasureTheory
open scoped ENNReal

namespace LogLogJam

/-- **Corollary 5.7** (arXiv:2607.12983, version of November 3, 2026, sha256 97b751ca…, Corollary 5.7, p.25): "J̄_t = J̄_{t−1} + E_{θ,H_{t−1}}[J_{M_t}(θ)]."

Written for `t + 1` in place of `t` (`1 ≤ t + 1 ≤ T`). For the randomized measurement `M_{t+1}`
chosen at `H_t`, `J_{M_{t+1}}(θ)` is the Fisher information of the pair (seed, outcome), i.e. the
average of `J_W(θ)` over the seed law. -/
theorem corollary_5_7 {T : ℕ} (P : GaussProtocol T) (lam : ℝ) (hlam : 1 < lam) (t : ℕ)
    (ht : t + 1 ≤ T) :
    Jbar lam P (t + 1) =
      Jbar lam P t + ENNReal.ofReal (1 / Real.pi) * ∫⁻ θ in Set.Ico 0 Real.pi,
        histInt lam θ P t (fun H => ∫⁻ s, measFisher lam s.1 s.2 θ ∂(P.seed t H)) := by sorry

end LogLogJam
