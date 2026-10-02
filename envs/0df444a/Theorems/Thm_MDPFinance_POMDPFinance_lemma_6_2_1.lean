-- Prove2me | Theorems.Thm_MDPFinance_POMDPFinance_lemma_6_2_1
-- name    : MDPFinance.POMDPFinance.lemma_6_2_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:36:27.565989+00:00
-- url     : https://prove2.me/theorems/4d819664-8350-4f6e-9248-477dae1b8264
-- title:
--   Lemma 6.2.1 — the mean-variance auxiliary sequence stays strictly between 0 and 1
-- statement:
--   The recursion (6.7) that drives the mean-variance solution (`MDPFinance.POMDPFinance.dRem`)
--   produces a sequence $(d_k)$ that is always a genuine probability-like quantity: for every number
--   of remaining stages $k$ from $1$ to $N$ and every belief $\rho$, $0 < d_k(\rho) < 1$. This is the
--   fact that makes the mean-variance formulas of Theorem 6.2.3 well-posed — in particular, it
--   guarantees the constant $d_0(Q_0)/(1-d_0(Q_0))$ appearing in the variance formula and in the
--   Lagrange multiplier $\lambda^*$ is a well-defined positive number.
--
--   The bound rests on Assumption FM(iii) (the return covariance matrix is positive definite for
--   every unobservable state $y$) together with FM(ii) (some coordinate has an everywhere-nonzero
--   mean return): together they guarantee the matrix $C_{k}(\rho)$ appearing in the recursion is
--   genuinely invertible and the quadratic form $\ell_k(\rho)^\top C_k(\rho)^{-1}\ell_k(\rho)$ is
--   strictly between $0$ and $d_{k-1}(\rho)$ (rather than merely bounded).
--
--   **Moderation note.** Under Assumption (FM) (`MeanVarianceMarket`) and for $\rho\in\mathbb P(E_Y)$; the draft's version for an arbitrary market is false.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 185, Lemma 6.2.1

import Mathlib
import Definitions.Def_MDPFinance_POMDPFinance_Filter
import Definitions.Def_MDPFinance_POMDPFinance_MeanVariance

open MeasureTheory ProbabilityTheory

namespace MDPFinance.POMDPFinance

/-- Lemma 6.2.1 (Bäuerle–Rieder, p. 185, PDF 198), Assumption `FM` of §6.2 in force (in
particular (ii) a coordinate with everywhere-nonzero mean return, (iii) the return covariance
matrix positive definite for every `y`). For all `n = 0,1,\dots,N-1` and `\rho \in ℙ(E_Y)` it
holds that `0 < d_n(\rho) < 1`. Restated with `k := N-n` stages remaining (`k` ranges over
`1,\dots,N`, matching `n` over `0,\dots,N-1`), against the closed-form recursion `dRem`, for
`ρ ∈ ℙ(E_Y)`; Assumption (FM) is the field set of `MeanVarianceMarket`. -/
theorem lemma_6_2_1 {EY : Type*} [MeasurableSpace EY] {d : ℕ} (M : FilterMarket EY d)
    (Fd : FilterOp M) (Mv : MeanVarianceMarket M) (N : ℕ) :
    ∀ k, 1 ≤ k → k ≤ N → ∀ ρ : Measure EY, IsProbabilityMeasure ρ →
      0 < dRem M Fd k ρ ∧ dRem M Fd k ρ < 1 := by sorry

end MDPFinance.POMDPFinance
