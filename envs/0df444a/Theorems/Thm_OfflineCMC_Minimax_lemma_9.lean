-- Prove2me | Theorems.Thm_OfflineCMC_Minimax_lemma_9
-- name    : OfflineCMC.Minimax.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:39:14.146417+00:00
-- url     : https://prove2.me/theorems/6ed68d95-1a18-45d0-baca-23fe52c0bca5
-- title:
--   Lemma 9 (corrected: |Cov| ≤ 2φ_{i,j}·E|g(X_i,a_i)|·ess sup|f(X_j,a_j)|) — covariance inequality for φ-mixing
-- statement:
--   Let $\{(X_i,a_i)\}$ be a controlled Markov chain, and let $\phi_{i,j}$ be its uniform mixing coefficient of eq. (2.2) on the window up to time $m$. Let $0\le i<j\le m$, and let $f,g$ be real functions on $\chi\times\mathbb I$. Then
--   $$
--   \big|\mathrm{Cov}\big(f(X_j,a_j),g(X_i,a_i)\big)\big|\le 2\,\phi_{i,j}\;\mathbb E\big|g(X_i,a_i)\big|\;\operatorname*{ess\,sup}\big|f(X_j,a_j)\big|,
--   $$
--   where $\operatorname{ess\,sup}|f(X_j,a_j)|=\max\{|f(y)|:\mathbb P((X_j,a_j)=y)>0\}$.
--
--   This is the covariance inequality for uniformly mixing sequences in the $L^1$–$L^\infty$ form. The $L^1$ norm is on the earlier variable and the essential supremum on the later one. Summed over pairs of times, it bounds the variance of the visit counts.
--
--   **Formalization Note** $\mathrm{Cov}(U,V)=\mathbb E[UV]-\mathbb E[U]\,\mathbb E[V]$. All variables involved are bounded functions of finitely-valued measurable maps, so every integral is of an integrable function.
--
--   Differences from the source:
--   - correction: $|\mathrm{Cov}|\le\phi_{i,j}\,\mathbb E|f(X_j,a_j)-\mathbb E f(X_j,a_j)|\,\operatorname{ess\,sup}|g(X_i,a_i)|$ → $|\mathrm{Cov}|\le2\phi_{i,j}\,\mathbb E|g(X_i,a_i)|\,\operatorname{ess\,sup}|f(X_j,a_j)|$; reason: the printed inequality is false. Take $d=2$, one control, $M=[[1/2,1/2],[0,1]]$, $X_0$ uniform, $i=0$, $j=m=1$ and $f=g=\mathbb 1[\text{state }2]$. Then $\mathrm{Cov}=1/8$ and $\phi_{0,1}=1/4$, while $\mathbb E|f-\mathbb Ef|=3/8$, so the printed right side is $3/32<1/8$.
--   - correction: the second display, $|\mathrm{Cov}|\le\bar\eta_{i,j}\,\mathbb E|f-\mathbb Ef|\,\operatorname{ess\,sup}|g|$ "by Lemma 1" → not stated; reason: false. In the chain with persistent controls of Lemma 1's counterexample, $f=g=\mathbb 1[\text{control }1]$ gives $\mathrm{Cov}=1/4$ while $\bar\eta_{i,j}=0$.
--   - reading: $i,j$ unrestricted → $0\le i<j\le m$; reason: $\phi_{i,j}$ is defined for $i<j\le m$ (eq. (2.2))
-- source:
--   Banerjee, Honnappa & Rao, Offline Estimation of Controlled Markov Chains: Minimaxity and Sample Complexity, arXiv:2211.07092v5, p. 32, Lemma 9 (App. B.1)

import Mathlib
import Definitions.Def_OfflineCMC_Minimax_CMC
import Definitions.Def_OfflineCMC_Minimax_Model

namespace OfflineCMC.Minimax

open MeasureTheory

open Classical in
theorem lemma_9 {d k : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (C : CMC d k μ) (m i j : ℕ) (hij : i < j) (hjm : j ≤ m)
    (f g : Fin d × Fin k → ℝ) :
    |∫ ω, f (C.X j ω, C.a j ω) * g (C.X i ω, C.a i ω) ∂μ -
        (∫ ω, f (C.X j ω, C.a j ω) ∂μ) * ∫ ω, g (C.X i ω, C.a i ω) ∂μ| ≤
      2 * C.phi m i j * (∫ ω, |g (C.X i ω, C.a i ω)| ∂μ) *
        ⨆ y : Fin d × Fin k,
          (if 0 < μ.real {ω | (C.X j ω, C.a j ω) = y} then |f y| else 0) := by sorry

end OfflineCMC.Minimax
