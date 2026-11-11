-- Prove2me | Theorems.Thm_LogLogJam_eq_14
-- name    : LogLogJam.eq_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:27:38.442009+00:00
-- url     : https://prove2.me/theorems/b5159fb8-f9e6-4d9d-bdf1-1d024c965256
-- title:
--   Eq. (14) — $p_{\mathrm{succ}}\le\frac{2\pi\varepsilon}E(\frac1\pi+8\pi E\sqrt{\mathbb E G(H_T)})\le\frac{2\varepsilon}E+16\pi^2\varepsilon\sqrt{\mathbb E G(H_T)}$
-- statement:
--   Let $\lambda>1$ with energy $E>1$ and $\varepsilon\in(0,1/2)$. For every $T$-adaptive protocol with randomized Gaussian measurements,
--
--   $$
--   p_{\mathrm{succ}}\le\frac{2\pi\varepsilon}{E}\Big(\frac1\pi+8\pi E\sqrt{\mathbb E[G(H_T)]}\Big)\le\frac{2\varepsilon}{E}+16\pi^2\varepsilon\sqrt{\mathbb E[G(H_T)]} .
--   $$
--
--   Constant success probability therefore needs $\mathbb E[G(H_T)]=\Omega(1/\varepsilon^2)$.
--
--   Differences from the source:
--
--   - reading: “By Lemma 5.4” (no hypotheses printed) → $\varepsilon\in(0,1/2)$, $E>1$; reason: the hypotheses of Lemma 5.4 and Lemma 5.3, which the display applies
--   - encoding: a Gaussian measurement with seed $W\in\mathrm{Cov}_k$ applied to the quantum state $\rho_\theta^{\otimes k}$ → its classical outcome law, the density $f^W_\theta(y)=\exp(-y^\top D^{-1}y)/(\pi^k\sqrt{\det D})$ with $D=V_\theta\otimes I_k+W$; reason: §4.2 (p.17) defines a Gaussian measurement by this outcome law on Gaussian states, and every measurement in the statement is applied to copies of $\rho_\theta$; same instances
--   - generalization: Definition 4.4: the measurement map gives, at each history, a randomized Gaussian measurement on a number $k$ of copies fixed by the history → a Markov kernel from histories to pairs $(k,W)$, so $k$ may also be random given the history; the drawn seed is recorded in the observation; reason: Definition 4.4's protocols are the kernels whose $k$-marginal is a Dirac mass; continuous ensembles are allowed by p.17
--   - encoding: the protocol's maps (no regularity stated) → the seed kernels and the output map are measurable, and seeds lie in $\mathrm{Cov}_k$ almost surely; reason: without measurability the success probability is undefined; this excludes only undefined cases
--   - encoding: $\theta\in\mathbb T=\mathbb R/\pi\mathbb Z$, uniform law and integrals on $\mathbb T$ → $\theta\in\mathbb R$ with $\pi$-periodic objects; uniform law and integrals over $[0,\pi)$; reason: $V_{\lambda,\theta}$ is $\pi$-periodic, so $[0,\pi)$ is one period; same instances
--   - encoding: the trace distance $D_{\mathrm{tr}}(\rho_{\theta'},\rho_\theta)$ of quantum states → $\sqrt{1-2/\sqrt{\det(V_{\lambda,\theta}+V_{\lambda,\theta'})}}$; reason: Lemma 4.1 (pp.15–16) for pure zero-mean single-mode Gaussian states; same values
--   - encoding: probabilities, expectations and Fisher informations as real numbers → values in $[0,\infty]$ (lower Lebesgue integrals of nonnegative functions); reason: every quantity is a nonnegative integral; the extended value avoids junk zeros for non-integrable integrands and agrees with the real value when finite
--   - encoding: energy $E>1/2$ and $\lambda>1$ the solution of $E=\tfrac14(\lambda+\lambda^{-1})$ → $\lambda>1$ as the parameter, $E=\mathrm{energy}\,\lambda=(\lambda+\lambda^{-1})/4$; reason: $\lambda\mapsto(\lambda+\lambda^{-1})/4$ is a bijection from $(1,\infty)$ onto $(1/2,\infty)$; same instances
-- source:
--   Chen, Gong, Ye, Zhang, The log log jam in Gaussian state tomography, arXiv:2607.12983 (version of November 3, 2026, sha256 97b751ca…), §6.2, eq. (14), p.30 (PDF p.33)

import Mathlib
import Definitions.Def_LogLogJam_GaussProtocol

open scoped ENNReal

namespace LogLogJam

/-- **Eq. (14)** (arXiv:2607.12983, version of November 3, 2026, sha256 97b751ca…, §6.2, eq. (14), p.30): "The initial condition is G(H_0) = 1/(8πE)². By
Lemma 5.4, the success probability is at most
p_succ ≤ (2πε/E)(1/π + 8πE √E[G(H_T)]) ≤ 2ε/E + 16π²ε √E[G(H_T)]."

Both inequalities, for every protocol, under the hypotheses of Lemma 5.4 (`ε ∈ (0, 1/2)`, `E > 1`). -/
theorem eq_14 {T : ℕ} (P : GaussProtocol T) (lam ε : ℝ) (hlam : 1 < lam)
    (hE : 1 < energy lam) (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    succProb lam ε P ≤
        ENNReal.ofReal (2 * Real.pi * ε / energy lam) *
          (ENNReal.ofReal (1 / Real.pi) +
            ENNReal.ofReal (8 * Real.pi * energy lam) * (expG lam P) ^ (1 / 2 : ℝ)) ∧
      ENNReal.ofReal (2 * Real.pi * ε / energy lam) *
          (ENNReal.ofReal (1 / Real.pi) +
            ENNReal.ofReal (8 * Real.pi * energy lam) * (expG lam P) ^ (1 / 2 : ℝ)) ≤
        ENNReal.ofReal (2 * ε / energy lam) +
          ENNReal.ofReal (16 * Real.pi ^ 2 * ε) * (expG lam P) ^ (1 / 2 : ℝ) := by sorry

end LogLogJam
