-- Prove2me | Theorems.Thm_OnlineGND_ineq_16
-- name    : OnlineGND.ineq_16
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:21:01.336247+00:00
-- url     : https://prove2.me/theorems/c6f9a6a2-cf1c-4e47-801a-3480a6172181
-- title:
--   The inequality at (16) — $(X+Y)^{\alpha-1}\le e X^{\alpha-1}+\alpha^{\alpha-1}Y^{\alpha-1}$
-- statement:
--   For every real $\alpha\ge1$ and all $X,Y\ge0$,
--   $$(X+Y)^{\alpha-1}\le e\cdot X^{\alpha-1}+\alpha^{\alpha-1}\cdot Y^{\alpha-1},$$
--   where $e$ is Euler's number.
--
--   The paper takes it from Lemma 4.1 of Awerbuch et al. (1995) with $c=e$; it is the step (16) in the analysis of the integral online algorithm, applied with $\alpha=\alpha_e$, $X=\ell_e$, $Y=w_{i,e}$.
--
--   **Formalization Note** Powers are `Real.rpow`, with $0^0=1$, so at $\alpha=1$ the claim reads $1\le e+1$.
--
--   Differences from the source:
--   - encoding: $X^{\alpha-1}$ at $X=0$, $\alpha=1$ → the value $1$ (`Real.rpow`); reason: Lean convention $0^0=1$, the usual reading of the paper's formula; it changes no instance with $\alpha>1$ or $X,Y>0$
-- source:
--   Nagarajan & Wang, Online Generalized Network Design Under (Dis)Economies of Scale, arXiv:2007.07721v1, §4, the sentence after (19), p.11 (from Lemma 4.1 of [AAG+95])

import Mathlib

namespace OnlineGND

/-- **The inequality used at (16)** (Nagarajan & Wang, arXiv:2007.07721v1, §4, p.11, from Lemma 4.1 of
[AAG+95] with `c = e`): for `α ≥ 1` and `X, Y ≥ 0`,
`(X + Y)^{α−1} ≤ e · X^{α−1} + α^{α−1} · Y^{α−1}`.

**Formalization Note.** `Real.rpow`, with `0^0 = 1`: at `α = 1` the claim reads `1 ≤ e + 1`. -/
theorem ineq_16 (α X Y : ℝ) (hα : 1 ≤ α) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    (X + Y) ^ (α - 1) ≤ Real.exp 1 * X ^ (α - 1) + α ^ (α - 1) * Y ^ (α - 1) := by sorry

end OnlineGND
