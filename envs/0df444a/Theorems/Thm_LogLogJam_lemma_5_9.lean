-- Prove2me | Theorems.Thm_LogLogJam_lemma_5_9
-- name    : LogLogJam.lemma_5_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:27:20.155209+00:00
-- url     : https://prove2.me/theorems/589c4686-4d43-488e-9b37-cc4f948be94c
-- title:
--   Lemma 5.9 — $\bar J_t=\mathbb E_{H_t}F(p_{H_t})$
-- statement:
--   For every $T$-adaptive protocol with randomized Gaussian measurements on the squeezed family ($\lambda>1$) and every $t\le T$, the expected Fisher information equals the expected Fisher information of the posterior:
--
--   $$
--   \bar J_t=\mathbb E_{H_t}\,F(p_{H_t}),
--   $$
--
--   the expectation being over the law of $H_t$ when $\theta$ is uniform on $\mathbb T$. This lets the argument track the posterior, whose information can be bounded history by history.
--
--   Differences from the source:
--
--   - encoding: a Gaussian measurement with seed $W\in\mathrm{Cov}_k$ applied to the quantum state $\rho_\theta^{\otimes k}$ → its classical outcome law, the density $f^W_\theta(y)=\exp(-y^\top D^{-1}y)/(\pi^k\sqrt{\det D})$ with $D=V_\theta\otimes I_k+W$; reason: §4.2 (p.17) defines a Gaussian measurement by this outcome law on Gaussian states, and every measurement in the statement is applied to copies of $\rho_\theta$; same instances
--   - generalization: Definition 4.4: the measurement map gives, at each history, a randomized Gaussian measurement on a number $k$ of copies fixed by the history → a Markov kernel from histories to pairs $(k,W)$, so $k$ may also be random given the history; the drawn seed is recorded in the observation; reason: Definition 4.4's protocols are the kernels whose $k$-marginal is a Dirac mass; continuous ensembles are allowed by p.17
--   - encoding: the protocol's maps (no regularity stated) → the seed kernels and the output map are measurable, and seeds lie in $\mathrm{Cov}_k$ almost surely; reason: without measurability the success probability is undefined; this excludes only undefined cases
--   - encoding: $\theta\in\mathbb T=\mathbb R/\pi\mathbb Z$, uniform law and integrals on $\mathbb T$ → $\theta\in\mathbb R$ with $\pi$-periodic objects; uniform law and integrals over $[0,\pi)$; reason: $V_{\lambda,\theta}$ is $\pi$-periodic, so $[0,\pi)$ is one period; same instances
--   - encoding: probabilities, expectations and Fisher informations as real numbers → values in $[0,\infty]$ (lower Lebesgue integrals of nonnegative functions); reason: every quantity is a nonnegative integral; the extended value avoids junk zeros for non-integrable integrands and agrees with the real value when finite
--   - encoding: energy $E>1/2$ and $\lambda>1$ the solution of $E=\tfrac14(\lambda+\lambda^{-1})$ → $\lambda>1$ as the parameter, $E=\mathrm{energy}\,\lambda=(\lambda+\lambda^{-1})/4$; reason: $\lambda\mapsto(\lambda+\lambda^{-1})/4$ is a bijection from $(1,\infty)$ onto $(1/2,\infty)$; same instances
-- source:
--   Chen, Gong, Ye, Zhang, The log log jam in Gaussian state tomography, arXiv:2607.12983 (version of November 3, 2026, sha256 97b751ca…), Lemma 5.9, p.26 (PDF p.29)

import Mathlib
import Definitions.Def_LogLogJam_GaussProtocol

open scoped ENNReal

namespace LogLogJam

/-- **Lemma 5.9** (arXiv:2607.12983, version of November 3, 2026, sha256 97b751ca…, Lemma 5.9, p.26): "J̄_t = E_{H_t} F(p_{H_t})."

`E_{H_t}` is the expectation under the law of the history with `θ` uniform on `𝕋`. -/
theorem lemma_5_9 {T : ℕ} (P : GaussProtocol T) (lam : ℝ) (hlam : 1 < lam) (t : ℕ)
    (ht : t ≤ T) :
    Jbar lam P t =
      ENNReal.ofReal (1 / Real.pi) * ∫⁻ θ in Set.Ico 0 Real.pi, histInt lam θ P t (postFisher lam) := by sorry

end LogLogJam
