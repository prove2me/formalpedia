-- Prove2me | Theorems.Thm_MNLBandit_UCB_corollary_D_1
-- name    : MNLBandit.UCB.corollary_D_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:09:26.508983+00:00
-- url     : https://prove2.me/theorems/24c92bd4-7446-45f0-a562-be4d63594e5b
-- title:
--   Corollary D.1, p. 56 — deviation bounds 6/(Nℓ²), 4/(Nℓ²), 3/(Nℓ²) for the mean of geometric variables with μ ≤ 1
-- statement:
--   Let $X_1,\dots,X_n$ ($n\ge1$) be i.i.d. geometric random variables with parameter $p\in(0,1]$, $\Pr(X_i=m)=(1-p)^mp$, let $\mu=\frac{1-p}{p}$ and $\bar X=\frac1n\sum_{i=1}^nX_i$. Let $N,\ell\ge1$ be integers and write $\lambda=\log(\sqrt N\ell+1)$. If $\mu\le1$, then
--   $$
--   \begin{aligned}
--   &\mathcal P\Big(|\bar X-\mu|>\sqrt{\frac{48\bar X\lambda}{n}}+\frac{48\lambda}{n}\Big)\le\frac{6}{N\ell^2},\\
--   &\mathcal P\Big(|\bar X-\mu|\ge\sqrt{\frac{24\mu\lambda}{n}}+\frac{48\lambda}{n}\Big)\le\frac{4}{N\ell^2},\\
--   &\mathcal P\Big(\bar X\ge\frac{3\mu}{2}+\frac{48\lambda}{n}\Big)\le\frac{3}{N\ell^2}.
--   \end{aligned}
--   $$
--   Here $N$ and $\ell$ are free parameters: in the paper's application $N$ is the number of products and $\ell$ the epoch index, and the bounds are summed over the at most $\ell$ possible sample sizes in the proof of Lemma A.2.
--
--   **Formalization Note.** The page says "for all $n=1,2,\dots$" for the first two bounds; the third is stated for all $n\ge1$ in the same way. The sample is the product of $n$ copies of Mathlib's `geometricMeasure p`.
-- source:
--   Agrawal, Avadhanula, Goyal, Zeevi, MNL-Bandit: A Dynamic Learning Approach to Assortment Selection, arXiv:1706.03880v2, p. 56, Corollary D.1

import Mathlib

namespace MNLBandit.UCB

open MeasureTheory ProbabilityTheory

theorem corollary_D_1 (n : ℕ) (hn : 1 ≤ n) (N ℓ : ℕ) (hN : 1 ≤ N) (hℓ : 1 ≤ ℓ)
    (p : unitInterval) (hp : p ≠ 0) :
    let μ : ℝ := (1 - (p : ℝ)) / (p : ℝ)
    let P : Measure (Fin n → ℕ) := Measure.pi (fun _ : Fin n => geometricMeasure p)
    let Xbar : (Fin n → ℕ) → ℝ := fun x => (∑ k, (x k : ℝ)) / (n : ℝ)
    let lg : ℝ := Real.log (Real.sqrt N * ℓ + 1)
    μ ≤ 1 →
      P {x | |Xbar x - μ| > Real.sqrt (48 * Xbar x * lg / n) + 48 * lg / n} ≤
          ENNReal.ofReal (6 / (N * ℓ ^ 2)) ∧
      P {x | |Xbar x - μ| ≥ Real.sqrt (24 * μ * lg / n) + 48 * lg / n} ≤
          ENNReal.ofReal (4 / (N * ℓ ^ 2)) ∧
      P {x | Xbar x ≥ 3 * μ / 2 + 48 * lg / n} ≤ ENNReal.ofReal (3 / (N * ℓ ^ 2)) := by sorry

end MNLBandit.UCB
