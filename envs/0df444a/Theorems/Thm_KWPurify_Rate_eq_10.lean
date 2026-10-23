-- Prove2me | Theorems.Thm_KWPurify_Rate_eq_10
-- name    : KWPurify.Rate.eq_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:29:49.760406+00:00
-- url     : https://prove2.me/theorems/cc613281-e262-4c9e-84ab-0c73399f3da8
-- title:
--   Eq. (10) — $\lim_{N\to\infty,\,M/N\to\mu} F^{\max}_{\mathrm{all}}(N,M) = \Phi(\mu)$
-- statement:
--   Let $0 < \lambda < 1$ be the noise parameter of the depolarizing channel $R_*\sigma = \lambda\sigma + (1-\lambda)\mathbb 1/2$, and let $\mu > 0$. Let $F^{\max}_{\mathrm{all}}(N,M)$ be the optimal worst-case all-qubit fidelity of a quantum channel taking $N$ noisy copies $(R_*\sigma)^{\otimes N}$ of an unknown pure qubit state $\sigma$ to $M$ qubits, measured against $\sigma^{\otimes M}$. Then for all sequences $N_k \to \infty$ and $M_k$ with $M_k/N_k \to \mu$,
--   $$\lim_{k\to\infty} F^{\max}_{\mathrm{all}}(N_k,M_k) = \Phi(\mu) = \begin{cases} \dfrac{2\lambda^2}{2\lambda^2+\mu(1-\lambda)} & \mu\le\lambda,\\[2mm] \dfrac{2\lambda^2}{\mu(1+\lambda)} & \mu\ge\lambda.\end{cases}$$
--
--   Since $\Phi(\mu) < 1$ for every $\mu > 0$, no purification procedure with positive output rate reaches fidelity one in the all-qubit sense, while every fidelity level below one is reached at some positive rate.
--
--   **Formalization Note** The supremum is over all channels (finite Kraus families, i.e. all CPTP maps) and the infimum over all unit vectors $\varphi \in \mathbb C^2$, with the noise applied to each of the $N$ input copies. The limit "$N\to\infty$, $M/N\to\mu$" is stated along every sequence, which is the strongest reading. $\lambda$ is written `lam`.
-- source:
--   Keyl & Werner, The Rate of Optimal Purification procedures, arXiv:quant-ph/9910124v1, p. 5, eq. (10) (proved at the end of §6.3, p. 22)

import Mathlib
import Definitions.Def_KWPurify_Rate_Model

open Filter Topology

namespace KWPurify.Rate
theorem eq_10 (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1) (μ : ℝ) (hμ : 0 < μ)
    (N M : ℕ → ℕ) (hN : Tendsto (fun k => (N k : ℝ)) atTop atTop)
    (hMN : Tendsto (fun k => (M k : ℝ) / (N k : ℝ)) atTop (𝓝 μ)) :
    Tendsto (fun k => maxAllFidelity lam (N k) (M k)) atTop (𝓝 (ratePhi lam μ)) := by sorry
end KWPurify.Rate
