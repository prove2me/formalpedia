-- Prove2me | Theorems.Thm_MDPFinance_MeanVariance_mvd_bounds
-- name    : MDPFinance.MeanVariance.mvd_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T22:08:31.004966+00:00
-- url     : https://prove2.me/theorems/f622eaf0-231c-45d7-959e-b9a271547f04
-- title:
--   Lemma 4.6.4 — the recursively-defined sequence $d_n$ stays in $(0,1)$
-- statement:
--   Under Assumption (FM) — the covariance matrix $\Sigma_n := C_n - \mathbb{E}[R_n]
--   \mathbb{E}[R_n]^\top$ is positive definite and $\mathbb{E}[R_n]\ne0$ for $n=1,\dots,N$ — the
--   sequence defined by $d_N:=1$, $d_n := d_{n+1}(1-\ell_{n+1})$ (Eq. (4.34)) satisfies
--   $0 < d_n < 1$ for every $n=0,\dots,N-1$.
--
--   This technical bound is what makes Theorem 4.6.6's closed form well-defined: the mean-variance
--   frontier's slope $\sqrt{(1-d_0)/d_0}$ and the optimal policy's denominator $1-d_0$ both need
--   $d_0\in(0,1)$ strictly.
--
--   **Formalization Note.** Assumption (FM) is carried as the two explicit hypotheses
--   `hCov_posdef`/`hEvec_ne` on the covariance matrix and mean vector, rather than folded into
--   `MVMarket`'s own fields, since it is a standing hypothesis of §4.6 specifically (chunk-local),
--   not part of the general market model shared with `04a`-`04d`.
--
--   **Formalization Note (moderation).** Assumption (FM) is carried by the model (the section's
--   standing assumption), so it is no longer repeated as separate hypotheses.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 121, PDF 135, Lemma 4.6.4

import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_MVMarket
import Definitions.Def_MDPFinance_MeanVariance_MVAuxiliary

open MeasureTheory ProbabilityTheory

namespace MDPFinance.MeanVariance

/-- Lemma 4.6.4 (Bäuerle–Rieder, p. 121, PDF 135). Let `(d_n)` satisfy `d_N := 1`,
`d_n := d_{n+1}(1-ℓ_{n+1})` for `n < N` (Eq. (4.34)). Under the section's standing Assumption
(FM) (carried by the model: positive definite covariance matrices and `𝔼 R_n ≠ 0`), it holds
`0 < d_n < 1` for all `n = 0,…,N-1`. -/
theorem mvd_bounds {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (M : MVMarket Ω d)
    (dseq : ℕ → ℝ) (hdN : dseq M.N = 1)
    (hdrec : ∀ n < M.N, dseq n = dseq (n + 1) * (1 - M.ell (n + 1))) :
    ∀ n < M.N, 0 < dseq n ∧ dseq n < 1 := by sorry

end MDPFinance.MeanVariance
