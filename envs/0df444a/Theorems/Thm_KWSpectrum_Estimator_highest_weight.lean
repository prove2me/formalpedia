-- Prove2me | Theorems.Thm_KWSpectrum_Estimator_highest_weight
-- name    : KWSpectrum.Estimator.highest_weight
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:33:13.672863+00:00
-- url     : https://prove2.me/theorems/17006c53-05e0-4354-9b3b-571ec3eb29cf
-- title:
--   §III, p. 3 — the frame $Y$ is a weight of multiplicity one and the highest weight (dominance) of $\pi_Y$
-- statement:
--   Let $Y$ be a Young frame with $N$ boxes and at most $d$ rows, with row lengths $Y_1 \ge \dots \ge Y_d$. Weights of $\pi_Y$ are read, as in eq. (20), as contents of semistandard fillings of $Y$ with entries in $\{1,\dots,d\}$.
--
--   1. **Multiplicity one.** Exactly one semistandard filling of $Y$ has content $(Y_1,\dots,Y_d)$.
--   2. **Highest weight.** Every semistandard filling of $Y$ has a content $\mu$ dominated by $Y$:
--   $$\mu_1 + \dots + \mu_k \le Y_1 + \dots + Y_k \quad (k = 1, 2, \dots), \qquad \mu_1 + \dots + \mu_d = Y_1 + \dots + Y_d.$$
--
--   Dominance is the order in which the paper uses "$Y \rhd \mu$": for every decreasing $h$ it gives $\mu\cdot h \le Y\cdot h$, so $e^{Y\cdot h}$ is the largest exponential in (20).
--
--   **Formalization Note** Rows and entries are zero-based. The prefix sums run over the indices $i < k$ for every natural number $k$.
--
--   Differences from the source:
--   - reading: "$Y$ is the maximum among all weights of $\pi_Y$, in the $\rhd$-ordering from Equation (6)" → $Y$ dominates every weight (prefix sums); reason: (6) orders the entries of one vector, and the difference order $Y - \mu \rhd 0$ is false: $Y = (2,1,0)$ has the weight $\mu = (1,2,0)$ (the filling with rows $1\,2$ and $2$), and $Y - \mu = (1,-1,0)$ is not decreasing; the use on p. 4 ($Y\cdot h \ge \mu\cdot h$ for every decreasing $h$) is exactly dominance.
--   - reading: weights and multiplicities of $\pi_Y$ → contents of semistandard fillings and their numbers; reason: the identification of eq. (20), posed as its own milestone.
-- source:
--   Keyl & Werner, Estimating the spectrum of a density operator, arXiv:quant-ph/0102027v1, p. 3, §III (paragraph after eq. (16): "One particular weight (with multiplicity one) is the Young frame Y itself ...")

import Mathlib
import Definitions.Def_KWSpectrum_Estimator_Model

namespace KWSpectrum.Estimator

open QAlgorithms QAlgorithms.Schur

/-- Keyl–Werner, arXiv:quant-ph/0102027v1, §III, p. 3 (highest weight), with weights read as
contents of semistandard fillings (eq. (20)): (i) the Young frame `Y` is a weight of
multiplicity one, i.e. exactly one semistandard filling of `Y` with entries in `{0, …, d − 1}`
has content `(Y₁, …, Y_d)`; (ii) `Y` dominates every weight: for every semistandard filling with
content `μ`, `μ₁ + ⋯ + μ_k ≤ Y₁ + ⋯ + Y_k` for every `k`, with equality of the totals. -/
theorem highest_weight {d N : ℕ} (Y : Partition d N) :
    (∃! T : Y.val.cells → Fin d,
      IsSemistandardFilling Y T ∧ content Y T = fun i => Y.val.rowLen i.val) ∧
    ∀ T : Y.val.cells → Fin d, IsSemistandardFilling Y T →
      (∀ k : ℕ, ∑ i : Fin d with i.val < k, content Y T i ≤
          ∑ i : Fin d with i.val < k, Y.val.rowLen i.val) ∧
      ∑ i : Fin d, content Y T i = ∑ i : Fin d, Y.val.rowLen i.val := by sorry

end KWSpectrum.Estimator
