-- Prove2me | Theorems.Thm_IntermediateDisorder_PointToLine_discreteKernel_L2_bound
-- name    : IntermediateDisorder.PointToLine.discreteKernel_L2_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T04:42:54.028323+00:00
-- url     : https://prove2.me/theorems/5c015eb6-67e7-4350-98e8-46b82ed7a38e
-- title:
--   Lemma A.1 — $\sup_n\|n^{k/2}p_k^n\|_{L^2}\le C^k\|\varrho_k\|_{L^2}$
-- statement:
--   There exists a constant $C>0$ such that for all $k\ge0$,
--
--   $$\sup_{n\ge1}\big\|n^{k/2}p_k^n\big\|_{L^2([0,1]^k\times\mathbb R^k)}\le C^k\,\|\varrho_k\|_{L^2([0,1]^k\times\mathbb R^k)} .$$
--
--   Here $p_k^n$ is the discretized random walk kernel of Definition 5.1 and $\varrho_k$ the Brownian kernel. Together with the local limit theorem ($n^{k/2}p_k^n\to\varrho_k$ pointwise) this bound gives, by dominated convergence, $\|\varrho_k-n^{k/2}p_k^n\|_{L^2}\to0$ with a summable majorant in $k$, which is the analytic input of Proposition 5.3.
--
--   **Formalization Note** The constant is chosen before $k$ and $n$, as on the page. Norms are written as $L^2$ norms with values in $[0,\infty]$, so the inequality also asserts $n^{k/2}p_k^n\in L^2$. The page's second inequality, for the bridge kernels $p^n_{k|x}$ of Section 6.1, concerns the point-to-point partition functions and is outside this mission.
-- source:
--   Alberts, Khanin, Quastel, The intermediate disorder regime for directed polymers in dimension 1+1, arXiv:1202.4398v3, p. 37, Lemma A.1 (first inequality)

import Mathlib
import Definitions.Def_IntermediateDisorder_PointToLine_WienerChaos
import Definitions.Def_IntermediateDisorder_PointToLine_UStatistic

namespace IntermediateDisorder.PointToLine

open MeasureTheory

/-- Lemma A.1 (first inequality): there is a constant `C > 0` such that for all `k ≥ 0`,
`sup_{n ≥ 1} ‖n^{k/2} p_k^n‖_{L²} ≤ C^k ‖ϱ_k‖_{L²}`, norms on `[0,1]^k × ℝ^k`. -/
theorem discreteKernel_L2_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (k n : ℕ), 1 ≤ n →
      eLpNorm (fun z => (n : ℝ) ^ ((k : ℝ) / 2) * discreteKernel n k z) 2 (kernelMeasure k) ≤
        ENNReal.ofReal (C ^ k) * eLpNorm (rhoK k) 2 (kernelMeasure k) := by sorry

end IntermediateDisorder.PointToLine
