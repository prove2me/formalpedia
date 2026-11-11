-- Prove2me | Theorems.Thm_LogLogJam_lemma_6_1
-- name    : LogLogJam.lemma_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:23:56.000028+00:00
-- url     : https://prove2.me/theorems/54edf665-01ca-4dfb-b0a3-7cd6fb54e82f
-- title:
--   Lemma 6.1 — $\int_0^\pi J_W\le k\pi(4E-2)$, equality iff $\det W=1$ (corrected: equality iff $\det W=1$ only for $E>1/2$)
-- statement:
--   Let $\lambda\ge1$ (energy $E=\tfrac14(\lambda+\lambda^{-1})\ge1/2$), $k\ge1$ and $W\in\mathrm{Cov}_k$. Then
--
--   1. the averaged single-step Fisher information is bounded:
--   $$
--   \int_0^\pi J_W(\theta)\,d\theta\le k\pi(4E-2);
--   $$
--   2. if $\lambda>1$ (that is, $E>1/2$), equality holds if and only if $W$ is the covariance of a pure state, $\det W=1$;
--   3. if $\lambda=1$ (that is, $E=1/2$), equality holds for every $W\in\mathrm{Cov}_k$.
--
--   No Gaussian measurement on $k$ copies gains more than $k\pi(4E-2)$ Fisher information on average over the angle, whether or not it is entangled across copies.
--
--   Differences from the source:
--
--   - correction: for every $E\ge1/2$: equality iff $\det W=1$ → equality iff $\det W=1$ for $E>1/2$; at $E=1/2$ equality for every $W\in\mathrm{Cov}_k$; reason: at $E=1/2$, $\lambda=1$ and $V_\theta=I$ for every $\theta$, so $J_W\equiv0$; $k=1$, $W=2I_2\in\mathrm{Cov}_1$ has $\det W=4\ne1$ yet $\int J_W=0=k\pi(4E-2)$ (the proof's step “$\partial_\theta D_\theta$ is not singular” fails at $\lambda=1$)
--   - encoding: $E\ge1/2$ → $\lambda\ge1$ with $E=(\lambda+\lambda^{-1})/4$; reason: bijection of $[1,\infty)$ onto $[1/2,\infty)$
--   - encoding: $\int_0^\pi$ → integral over $[0,\pi)$; reason: same Lebesgue integral
--   - encoding: $J_W(\theta)=\mathbb E_{Y\sim f^W_\theta}[(\partial_\theta\log f^W_\theta(Y))^2]$ → `measFisher`, the Lebesgue integral $\int f^W_\theta(y)(\partial_\theta\log f^W_\theta(y))^2\,dy\in[0,\infty]$; reason: the same integral; not the closed form $\tfrac12\mathrm{tr}((D^{-1}\partial_\theta D)^2)$ quoted in the proof of Lemma 6.1
--   - encoding: probabilities, expectations and Fisher informations as real numbers → values in $[0,\infty]$ (lower Lebesgue integrals of nonnegative functions); reason: every quantity is a nonnegative integral; the extended value avoids junk zeros for non-integrable integrands and agrees with the real value when finite
--   - encoding: $V_\theta^{\oplus k}$ and $2k\times2k$ matrices on $k$ modes → index $\mathrm{Fin}\,2\times\mathrm{Fin}\,k$ in the q-then-p order, $V_\theta^{\oplus k}=V_\theta\otimes I_k$ (Kronecker, $2\times2$ block outside), $\Omega_k=[[0,I_k],[-I_k,0]]$; reason: the order the page itself uses for $V_\theta^{\oplus k}$ in Lemma 4.8, Lemma 4.6 and the proof of Lemma 6.1 (§4.2, p.17: the q-then-p reordering gives $V\otimes I_k$); a permutation of coordinates, same instances
-- source:
--   Chen, Gong, Ye, Zhang, The log log jam in Gaussian state tomography, arXiv:2607.12983 (version of November 3, 2026, sha256 97b751ca…), Lemma 6.1, p.28 (PDF p.31)

import Mathlib
import Definitions.Def_LogLogJam_Obs

open MeasureTheory
open scoped ENNReal

namespace LogLogJam

/-- **Lemma 6.1, corrected** (arXiv:2607.12983, version of November 3, 2026, sha256 97b751ca…, Lemma 6.1, p.28): "For every E ≥ 1/2, k ≥ 1, and W^{(k)} ∈ Cov_k,
we have ∫_0^π J_{W^{(k)}}(θ) dθ ≤ kπ(4E − 2), with the equality achieved if and only if the seed
covariance matrix W^{(k)} corresponds to a pure Gaussian state, that is, det(W^{(k)}) = 1."

Corrected statement: (a) the inequality for every `λ ≥ 1` (`E ≥ 1/2`); (b) for `λ > 1` (`E > 1/2`),
equality iff `det W = 1`; (c) for `λ = 1` (`E = 1/2`), equality for every `W ∈ Cov_k`.

**Formalization Note** The printed "only if" fails at `E = 1/2`: then `λ = 1`, `V_θ = I` for every
`θ`, so `J_W ≡ 0`; with `k = 1` and `W = 2I₂ ∈ Cov₁` (`det W = 4`) equality `0 = kπ(4E − 2)` holds.
`J_W` is the Fisher-information integral `measFisher`. -/
theorem lemma_6_1 (lam : ℝ) (hlam : 1 ≤ lam) (k : ℕ) (hk : 1 ≤ k) (W : Q k → Q k → ℝ)
    (hW : IsCov k (Matrix.of W)) :
    (∫⁻ θ in Set.Ico 0 Real.pi, measFisher lam k W θ ≤
        ENNReal.ofReal (k * Real.pi * (4 * energy lam - 2))) ∧
      (1 < lam → (∫⁻ θ in Set.Ico 0 Real.pi, measFisher lam k W θ =
        ENNReal.ofReal (k * Real.pi * (4 * energy lam - 2)) ↔ (Matrix.of W).det = 1)) ∧
      (lam = 1 → ∫⁻ θ in Set.Ico 0 Real.pi, measFisher lam k W θ =
        ENNReal.ofReal (k * Real.pi * (4 * energy lam - 2))) := by sorry

end LogLogJam
