-- Prove2me | Theorems.Thm_LiquidDemocracy_Upward_lemma_2
-- name    : LiquidDemocracy.Upward.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:24:38.689744+00:00
-- url     : https://prove2.me/theorems/e3ac8ac8-7e85-41cb-b623-37988021ecb9
-- title:
--   Lemma 2, p. 12 — the largest bin of the infinite Pólya urn after T steps is at most T^δ with probability 1 − o(1)
-- statement:
--   For $p\in(0,1)$ let $L^p_T$ be the largest number of balls in a bin after running the infinite Pólya urn process with attachment probability $p$ for $T$ steps. Then there is $\delta<1$, depending only on $p$, such that
--
--   $$\Pr\big[L^p_T\le T^\delta\big]\ \longrightarrow\ 1\qquad(T\to\infty).$$
--
--   The largest bin is thus sub-linear in the number of balls. Through the coupling between the urn and the Upward Delegation Model, this gives condition (1) of Lemma 1: no voter gathers a constant fraction of the votes.
--
--   **Formalization Note** The page's statement says "new-bin probability $p$", while the process defined just before it on the same page has attachment probability $p$ (new-bin probability $1-p$). The formalization uses the process as defined; since the claim is for every $p\in(0,1)$, the two readings of the statement only rename the parameter. $\delta$ is chosen after $p$ and before $T$; "$=1-o(1)$" is convergence to 1.
-- source:
--   Berinsky et al., Tracking Truth with Liquid Democracy, arXiv:2107.11868v3, p. 12, Lemma 2

import Mathlib
import Definitions.Def_LiquidDemocracy_Upward_Urn

namespace LiquidDemocracy.Upward

open MeasureTheory Filter Topology

/-- Lemma 2, p. 12: for every `p ∈ (0,1)` there is `δ < 1`, depending only on `p`, such that the
largest bin `L^p_T` of the infinite Pólya urn after `T` steps satisfies
`Pr[L^p_T ≤ T^δ] = 1 − o(1)`. -/
theorem lemma_2 (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ δ < (1 : ℝ), Tendsto (fun T : ℕ =>
      (urnLaw p T).real {s | (maxBin s : ℝ) ≤ (T : ℝ) ^ δ}) atTop (𝓝 1) := by sorry

end LiquidDemocracy.Upward
