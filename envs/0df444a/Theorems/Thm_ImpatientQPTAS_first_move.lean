-- Prove2me | Theorems.Thm_ImpatientQPTAS_first_move
-- name    : ImpatientQPTAS.first_move
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:01:45.478916+00:00
-- url     : https://prove2.me/theorems/c5de8dc2-fdd9-431e-9dcb-c0d91e02ec7a
-- title:
--   §2.1, p.8 — the computed first move (repaired)
-- statement:
--   Let $m>4$ be an integer and $e=1/m$. For every instance,
--   $$
--   (1-2e)\,X^{\tilde r}-\frac{e}{n}\,r_{\max}\le\tilde X .
--   $$
--   Here $\tilde X$ is the best rounded value of a first move among average customers and quitters, and $X^{\tilde r}$ is the corresponding value with the rounded rewards and the true departure probabilities.
--
--   This makes the step "we initially guess the identity of customer $i_1$" into a computation.
--
--   Differences from the source:
--   - reading: "we initially guess the identity of customer i₁", with a policy per realization of A₂ ∩ C_average, each rounded against its own r_max → the first move maximizes Q̃, computed once on the count vectors, rewards rounded once against the global r_max; reason: the paper gives no way to evaluate the guess within the time bound; a count vector summarizes a set only under one global rounding
-- source:
--   Segev, Near-Optimal Adaptive Policies for Serving Stochastically Departing Customers, arXiv:2209.13878v1, §2.1, p.8; Theorem 2.6, p.11

import Mathlib
import Definitions.Def_ImpatientQPTAS_Model
import Definitions.Def_ImpatientQPTAS_Classes
import Definitions.Def_ImpatientQPTAS_Rounding

namespace ImpatientQPTAS

/-- Segev, arXiv:2209.13878v1, §2.1, p.8, repaired: the computed first move loses only a factor `1 − 2e`.
With `e = 1/m`, `(1 − 2e)·X^{r̃} − (e/n)·r_max ≤ X̃`.

**Formalization Note.** This is the step "we initially guess the identity of customer i₁" made into a
computation. `X̃` (`Xt`) is the best rounded value of a first move, `X^{r̃}` (`Xval` at `r̃`) the same with
the true departure probabilities. -/
theorem first_move {n : ℕ} (m : ℕ) (hm : 4 < m) (I : Instance n) (hI : I.Standing) :
    (1 - 2 * (1 / (m : ℝ))) * Xval (1 / (m : ℝ)) I (rTilde (1 / (m : ℝ)) I) -
        1 / (m : ℝ) / (n : ℝ) * rmax I.r ≤ Xt (1 / (m : ℝ)) I := by sorry

end ImpatientQPTAS
