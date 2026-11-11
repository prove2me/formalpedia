-- Prove2me | Theorems.Thm_LogLogJam_eq_18
-- name    : LogLogJam.eq_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:27:24.23544+00:00
-- url     : https://prove2.me/theorems/b57e11e1-d3e6-4433-85c1-534b113656c8
-- title:
--   Eq. (18) — $\mathbb E[G(H_T)]\le f^{\circ S}(1/(8\pi E)^2)$
-- statement:
--   Let $\lambda>1$ with energy $E$ and $f(x)=x+\sqrt x$. For every $T$-adaptive protocol with randomized Gaussian measurements that uses at most $S$ copies,
--
--   $$
--   \mathbb E[G(H_T)]\le f^{\circ S}\big(G(H_0)\big)=f^{\circ S}\Big(\frac1{(8\pi E)^2}\Big).
--   $$
--
--   Since $f^{\circ S}(1/N)$ stays small until $S\approx\log_2\log_2N$ (Lemma 6.4), this is where the $\log\log E$ comes from.
--
--   Differences from the source:
--
--   - generalization: sample complexity: the maximum number of copies over consistent length-$T$ histories → `CopiesLe`: for every $\theta$, almost every length-$T$ history uses at most $S$ copies; reason: a weaker hypothesis: a bound on every consistent history implies the almost-sure bound
--   - encoding: a Gaussian measurement with seed $W\in\mathrm{Cov}_k$ applied to the quantum state $\rho_\theta^{\otimes k}$ → its classical outcome law, the density $f^W_\theta(y)=\exp(-y^\top D^{-1}y)/(\pi^k\sqrt{\det D})$ with $D=V_\theta\otimes I_k+W$; reason: §4.2 (p.17) defines a Gaussian measurement by this outcome law on Gaussian states, and every measurement in the statement is applied to copies of $\rho_\theta$; same instances
--   - generalization: Definition 4.4: the measurement map gives, at each history, a randomized Gaussian measurement on a number $k$ of copies fixed by the history → a Markov kernel from histories to pairs $(k,W)$, so $k$ may also be random given the history; the drawn seed is recorded in the observation; reason: Definition 4.4's protocols are the kernels whose $k$-marginal is a Dirac mass; continuous ensembles are allowed by p.17
--   - encoding: the protocol's maps (no regularity stated) → the seed kernels and the output map are measurable, and seeds lie in $\mathrm{Cov}_k$ almost surely; reason: without measurability the success probability is undefined; this excludes only undefined cases
--   - encoding: $\theta\in\mathbb T=\mathbb R/\pi\mathbb Z$, uniform law and integrals on $\mathbb T$ → $\theta\in\mathbb R$ with $\pi$-periodic objects; uniform law and integrals over $[0,\pi)$; reason: $V_{\lambda,\theta}$ is $\pi$-periodic, so $[0,\pi)$ is one period; same instances
--   - encoding: probabilities, expectations and Fisher informations as real numbers → values in $[0,\infty]$ (lower Lebesgue integrals of nonnegative functions); reason: every quantity is a nonnegative integral; the extended value avoids junk zeros for non-integrable integrands and agrees with the real value when finite
--   - encoding: energy $E>1/2$ and $\lambda>1$ the solution of $E=\tfrac14(\lambda+\lambda^{-1})$ → $\lambda>1$ as the parameter, $E=\mathrm{energy}\,\lambda=(\lambda+\lambda^{-1})/4$; reason: $\lambda\mapsto(\lambda+\lambda^{-1})/4$ is a bijection from $(1,\infty)$ onto $(1/2,\infty)$; same instances
-- source:
--   Chen, Gong, Ye, Zhang, The log log jam in Gaussian state tomography, arXiv:2607.12983 (version of November 3, 2026, sha256 97b751ca…), §6.2.2, eq. (18), p.32 (PDF p.35)

import Mathlib
import Definitions.Def_LogLogJam_GaussProtocol

open scoped ENNReal

namespace LogLogJam

/-- **Eq. (18)** (arXiv:2607.12983, version of November 3, 2026, sha256 97b751ca…, §6.2.2, eq. (18), p.32): "we arrive at the following upper bound for
E[G(H_T)]: E[G(H_T)] ≤ f^{∘S}(G(H_0)) = f^{∘S}(1/(8πE)²)", where `S` is the sample complexity of `P`
and `f(x) = x + √x`.

For every protocol using at most `S` copies and every `λ > 1` (`E > 1/2`). -/
theorem eq_18 {T : ℕ} (P : GaussProtocol T) (lam : ℝ) (hlam : 1 < lam) (S : ℕ)
    (hS : CopiesLe lam P S) :
    expG lam P ≤ ENNReal.ofReal (fIter S (1 / (8 * Real.pi * energy lam) ^ 2)) := by sorry

end LogLogJam
