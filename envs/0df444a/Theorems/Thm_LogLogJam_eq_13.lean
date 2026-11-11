-- Prove2me | Theorems.Thm_LogLogJam_eq_13
-- name    : LogLogJam.eq_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:25:45.318672+00:00
-- url     : https://prove2.me/theorems/4c525374-dedc-4776-82e2-499b8eac6c48
-- title:
--   Eq. (13) — $\mathbb E[G(H_t)\mid H_{t-1}]\le G(H_{t-1})+k\sqrt{G(H_{t-1})}$
-- statement:
--   Let $\lambda>1$ with energy $E$, let $H$ be a history whose seeds lie in $\mathrm{Cov}$, and let the next measurement use $k$ copies with seed $W\in\mathrm{Cov}_k$. With the potential $G(H)=(1+F(p_H))/(8\pi E)^2$,
--
--   $$
--   \mathbb E\big[G(H_t)\mid H_{t-1}=H\big]\le G(H)+k\sqrt{G(H)} .
--   $$
--
--   This is the one-step recursion behind the $\log\log E$ lower bound: starting from $G(H_0)=1/(8\pi E)^2$, one copy can at most add $\sqrt G$.
--
--   Differences from the source:
--
--   - generalization: the next measurement $M_t=\mathcal P_M(H_{t-1})$ of a protocol, possibly randomized, at a history $H_{t-1}$ of that protocol → every history $H$ whose seeds lie in $\mathrm{Cov}$ and every next seed $W\in\mathrm{Cov}_k$; reason: both sides are linear in the law of the next seed, so averaging the per-seed statement over a randomized measurement gives the source's; consistent histories of a protocol have seeds in $\mathrm{Cov}$
--   - encoding: a Gaussian measurement with seed $W\in\mathrm{Cov}_k$ applied to the quantum state $\rho_\theta^{\otimes k}$ → its classical outcome law, the density $f^W_\theta(y)=\exp(-y^\top D^{-1}y)/(\pi^k\sqrt{\det D})$ with $D=V_\theta\otimes I_k+W$; reason: §4.2 (p.17) defines a Gaussian measurement by this outcome law on Gaussian states, and every measurement in the statement is applied to copies of $\rho_\theta$; same instances
--   - encoding: $\theta\in\mathbb T=\mathbb R/\pi\mathbb Z$, uniform law and integrals on $\mathbb T$ → $\theta\in\mathbb R$ with $\pi$-periodic objects; uniform law and integrals over $[0,\pi)$; reason: $V_{\lambda,\theta}$ is $\pi$-periodic, so $[0,\pi)$ is one period; same instances
--   - encoding: probabilities, expectations and Fisher informations as real numbers → values in $[0,\infty]$ (lower Lebesgue integrals of nonnegative functions); reason: every quantity is a nonnegative integral; the extended value avoids junk zeros for non-integrable integrands and agrees with the real value when finite
--   - encoding: energy $E>1/2$ and $\lambda>1$ the solution of $E=\tfrac14(\lambda+\lambda^{-1})$ → $\lambda>1$ as the parameter, $E=\mathrm{energy}\,\lambda=(\lambda+\lambda^{-1})/4$; reason: $\lambda\mapsto(\lambda+\lambda^{-1})/4$ is a bijection from $(1,\infty)$ onto $(1/2,\infty)$; same instances
-- source:
--   Chen, Gong, Ye, Zhang, The log log jam in Gaussian state tomography, arXiv:2607.12983 (version of November 3, 2026, sha256 97b751ca…), §6.2, eq. (13), p.30 (PDF p.33)

import Mathlib
import Definitions.Def_LogLogJam_postFisher

open scoped ENNReal

namespace LogLogJam

/-- **Eq. (13)** (arXiv:2607.12983, version of November 3, 2026, sha256 97b751ca…, §6.2, eq. (13), p.30): "where k = k(H_{t−1}) is the number of copies used in
the measurement at history H_{t−1}. For clarity, define G(H_t) = (1+F(p_{H_t}))/(8πE)², the
recursion becomes E[G(H_t) | H_{t−1}] ≤ G(H_{t−1}) + k(H_{t−1}) √G(H_{t−1})."

For every `λ > 1` (`E > 1/2`), every history `H` whose seeds lie in `Cov` and every next Gaussian
measurement with seed `W ∈ Cov_k` on `k` copies.

**Formalization Note** A randomized next measurement averages both sides over its seed. -/
theorem eq_13 (lam : ℝ) (hlam : 1 < lam) {t : ℕ} (H : Hist t)
    (hH : ∀ i, IsCov (H i).1 (Matrix.of (H i).2.1)) (k : ℕ) (W : Q k → Q k → ℝ)
    (hW : IsCov k (Matrix.of W)) :
    nextCondExp lam H k W (Gpot lam) ≤ Gpot lam H + (k : ℝ≥0∞) * (Gpot lam H) ^ (1 / 2 : ℝ) := by sorry

end LogLogJam
