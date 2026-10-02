-- Prove2me | Theorems.Thm_MDPFinance_MeanVariance_mv_eq_mveq
-- name    : MDPFinance.MeanVariance.mv_eq_mveq
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:07:00.070982+00:00
-- url     : https://prove2.me/theorems/764d5558-56ac-4e3c-b035-899991ae2db1
-- title:
--   Lemma 4.6.1 — (MV) and (MV=) have the same optimal strategies
-- statement:
--   A strategy $\pi^*$ is optimal for (MV) if and only if it is optimal for (MV=): the
--   inequality constraint $\mathbb{E}_{x_0}^\pi[X_N]\ge\mu$ binds at the optimum, so relaxing it
--   to $\ge$ from $=$ changes nothing.
--
--   This licenses working with the equality-constrained problem throughout the rest of the section
--   (in particular the Lagrangian $L_{x_0}(\pi,\lambda) = \mathrm{Var}_{x_0}^\pi[X_N] +
--   2\lambda(\mu - \mathbb{E}_{x_0}^\pi[X_N])$ of Lemma 4.6.2 is built for the equality version),
--   without losing any optimal strategy of the original inequality-constrained (MV).
--
--   **Formalization Note.** Stated as the `Iff` the book proves (only the "if (MV) then $\mathbb E
--   =\mu$" direction needs an argument; the converse is immediate since (MV=)'s feasible set is a
--   subset of (MV)'s with the same objective, and its restriction argument is Proof content, not part
--   of the statement).
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 118, PDF 132, Lemma 4.6.1

import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_MVMarket

open MeasureTheory ProbabilityTheory

namespace MDPFinance.MeanVariance

/-- Lemma 4.6.1 (Bäuerle–Rieder, p. 118, PDF 132). A strategy `π*` is optimal for `(MV)` if and
only if `π*` is optimal for `(MV=)`. -/
theorem mv_eq_mveq {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (M : MVMarket Ω d)
    (πstar : ℕ → ℝ → (Fin d → ℝ)) :
    M.IsOptimalMV πstar ↔ M.IsOptimalMVeq πstar := by sorry

end MDPFinance.MeanVariance
