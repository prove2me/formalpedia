-- Prove2me | Theorems.Thm_LogLogJam_lemma_5_10
-- name    : LogLogJam.lemma_5_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:25:45.047994+00:00
-- url     : https://prove2.me/theorems/e61b4370-41c7-4b08-8c0c-1733df4e4b72
-- title:
--   Lemma 5.10 — chain rule and per-step bound for the posterior Fisher information
-- statement:
--   Let $\lambda>1$. Let $H$ be a history whose seeds lie in $\mathrm{Cov}$, and let the next measurement have seed $W\in\mathrm{Cov}_k$. Then
--
--   1. the posterior Fisher information obeys the chain rule
--   $$
--   \mathbb E\big[F(p_{H_t})\mid H_{t-1}=H\big]=F(p_H)+\mathbb E_{\theta\sim p_H}\big[J_W(\theta)\big];
--   $$
--   2. the information gained is controlled by the uniform average:
--   $$
--   \mathbb E_{\theta\sim p_H}\big[J_W(\theta)\big]\le\Big(1+\pi\sqrt{F(p_H)}\Big)\cdot\mathbb E_{\theta\sim\mathrm{Unif}(\mathbb T)}\big[J_W(\theta)\big].
--   $$
--
--   Together with Lemma 6.1 this gives the one-step recursion (13), valid even when the number of copies depends on the history.
--
--   Differences from the source:
--
--   - generalization: $\sup_M\mathbb E_{\theta\sim\mathrm{Unif}(\mathbb T)}[J_M(\theta)]$ in the second claim → $\mathbb E_{\theta\sim\mathrm{Unif}(\mathbb T)}[J_W(\theta)]$ for the measurement actually chosen; reason: this quantity is at most the supremum, so the Lean bound implies the printed one; it is what the proof (Hölder and Lemma 5.11) gives
--   - generalization: the next measurement $M_t=\mathcal P_M(H_{t-1})$ of a protocol, possibly randomized, at a history $H_{t-1}$ of that protocol → every history $H$ whose seeds lie in $\mathrm{Cov}$ and every next seed $W\in\mathrm{Cov}_k$; reason: both sides are linear in the law of the next seed, so averaging the per-seed statement over a randomized measurement gives the source's; consistent histories of a protocol have seeds in $\mathrm{Cov}$
--   - encoding: a Gaussian measurement with seed $W\in\mathrm{Cov}_k$ applied to the quantum state $\rho_\theta^{\otimes k}$ → its classical outcome law, the density $f^W_\theta(y)=\exp(-y^\top D^{-1}y)/(\pi^k\sqrt{\det D})$ with $D=V_\theta\otimes I_k+W$; reason: §4.2 (p.17) defines a Gaussian measurement by this outcome law on Gaussian states, and every measurement in the statement is applied to copies of $\rho_\theta$; same instances
--   - encoding: $J_W(\theta)=\mathbb E_{Y\sim f^W_\theta}[(\partial_\theta\log f^W_\theta(Y))^2]$ → `measFisher`, the Lebesgue integral $\int f^W_\theta(y)(\partial_\theta\log f^W_\theta(y))^2\,dy\in[0,\infty]$; reason: the same integral; not the closed form $\tfrac12\mathrm{tr}((D^{-1}\partial_\theta D)^2)$ quoted in the proof of Lemma 6.1
--   - encoding: $\theta\in\mathbb T=\mathbb R/\pi\mathbb Z$, uniform law and integrals on $\mathbb T$ → $\theta\in\mathbb R$ with $\pi$-periodic objects; uniform law and integrals over $[0,\pi)$; reason: $V_{\lambda,\theta}$ is $\pi$-periodic, so $[0,\pi)$ is one period; same instances
--   - encoding: probabilities, expectations and Fisher informations as real numbers → values in $[0,\infty]$ (lower Lebesgue integrals of nonnegative functions); reason: every quantity is a nonnegative integral; the extended value avoids junk zeros for non-integrable integrands and agrees with the real value when finite
--   - encoding: energy $E>1/2$ and $\lambda>1$ the solution of $E=\tfrac14(\lambda+\lambda^{-1})$ → $\lambda>1$ as the parameter, $E=\mathrm{energy}\,\lambda=(\lambda+\lambda^{-1})/4$; reason: $\lambda\mapsto(\lambda+\lambda^{-1})/4$ is a bijection from $(1,\infty)$ onto $(1/2,\infty)$; same instances
-- source:
--   Chen, Gong, Ye, Zhang, The log log jam in Gaussian state tomography, arXiv:2607.12983 (version of November 3, 2026, sha256 97b751ca…), Lemma 5.10, p.26 (PDF p.29)

import Mathlib
import Definitions.Def_LogLogJam_postFisher

open MeasureTheory
open scoped ENNReal

namespace LogLogJam

/-- **Lemma 5.10** (arXiv:2607.12983, version of November 3, 2026, sha256 97b751ca…, Lemma 5.10, p.26): "Conditioned on history H_{t−1}, let M_t = P_M(H_{t−1})
be the next measurement. Then E[F(p_{H_t}) | H_{t−1}] = F(p_{H_{t−1}}) + E_{θ∼p_{H_{t−1}}}[J_{M_t}(θ)].
(10) Furthermore, E_{θ∼p_{H_{t−1}}}[J_{M_t}(θ)] ≤ (1 + π √F(p_{H_{t−1}})) · sup_M E_{θ∼Unif(𝕋)}[J_M(θ)]."

For every history `H` whose seeds lie in `Cov` and every next Gaussian measurement with seed
`W ∈ Cov_k`: identity (10), and the second bound with `E_{θ∼Unif}[J_W(θ)]` in place of the supremum.

**Formalization Note** A randomized next measurement averages both sides over its seed. -/
theorem lemma_5_10 (lam : ℝ) (hlam : 1 < lam) {t : ℕ} (H : Hist t)
    (hH : ∀ i, IsCov (H i).1 (Matrix.of (H i).2.1)) (k : ℕ) (W : Q k → Q k → ℝ)
    (hW : IsCov k (Matrix.of W)) :
    nextCondExp lam H k W (postFisher lam) =
        postFisher lam H +
          ∫⁻ θ in Set.Ico 0 Real.pi, ENNReal.ofReal (post lam H θ) * measFisher lam k W θ ∧
      ∫⁻ θ in Set.Ico 0 Real.pi, ENNReal.ofReal (post lam H θ) * measFisher lam k W θ ≤
        (1 + ENNReal.ofReal Real.pi * (postFisher lam H) ^ (1 / 2 : ℝ)) *
          (ENNReal.ofReal (1 / Real.pi) * ∫⁻ θ in Set.Ico 0 Real.pi, measFisher lam k W θ) := by sorry

end LogLogJam
