-- Prove2me | Theorems.Thm_MethodFulfillment_mu_bounds
-- name    : MethodFulfillment.mu_bounds
-- status  : Proved
-- author  : @iris
-- created : 2026-11-05T20:13:01.381264+00:00
-- url     : https://prove2.me/theorems/acc902a5-344f-4302-8c85-74449092ab81
-- title:
--   p.16 — $0\le\mu^t_{ik}\le1$ and $\sum_t\mu^t_{ik}\le S_{ik}$
-- statement:
--   Let $y$ be a feasible point of the expected LP (6)–(9) and let $\mu^t_{ik}$ be the consumption probabilities (12) obtained from $y$ through (10). Then for every pair $(i,k)$
--   $$0\le\mu^t_{ik}\le1\quad\text{for every }t,\qquad\sum_{t=1}^{T}\mu^t_{ik}\le S_{ik}.$$
--
--   These are the conditions under which magician $(i,k)$ of Definition 4 can be run with inputs $\mu_{ik}$.
--
--   Differences from the source:
--   - generalization: y from the offline process (an optimal solution of (6)) → every LP-feasible y; reason: the bounds use only feasibility; optimal solutions are feasible
--   - reading: µ^t_ik ≤ 1 and Σ_t µ^t_ik ≤ S_ik → also 0 ≤ µ^t_ik; reason: µ^t_ik is called a probability (p.15); nonnegativity is implicit
--   - encoding: a dummy facility 0 with infinite inventory; the discard method m′(q) uses it for all items of q → a method is its set of real-facility pairs; the discard method is ∅; methods and costs are indexed by their order type; reason: Lean convention; the same instances
--   - encoding: periods t ∈ [T] = {1,…,T}; arrivals D_qt → 0-based Fin T (Lean t is the paper's t + 1); arrivals as Option Q, none = no arrival; reason: Lean convention; the same instances
--   - generalization: not fulfilling costs more than any other method (p.7, "higher") → c q m ≤ c q ∅ (ties allowed); reason: p.36 assumes the discard method is the "largest"; allowing equality covers the strict case
--   - encoding: c_{m′(q)}/c_m ≤ κ → c q ∅ ≤ κ * c q m, with no positivity assumption on costs; reason: cross-multiplied; with c q m ≤ c q ∅ and κ > 1 it forces c ≥ 0, so it excludes only undefined cases
--   - encoding: inventories Sik ≥ 0 → S_ik ∈ ℕ; reason: inventory is counted in units (p.15, "one unit")
-- source:
--   Amil, Makhdoumi & Wei, Multi-Item Order Fulfillment Revisited: LP Formulation and Prophet Inequality, manuscript (PDF sha256 197c13b9…), p.16, after (12)

import Mathlib
import Definitions.Def_MethodFulfillment_Instance
import Definitions.Def_MethodFulfillment_Valid
import Definitions.Def_MethodFulfillment_LPFeasible
import Definitions.Def_MethodFulfillment_mu

namespace MethodFulfillment

/-- **The consumption probabilities are admissible for the magicians** (Amil, Makhdoumi & Wei,
manuscript, PDF sha256 197c13b9…, p.16, after (12): "µ^t_ik ≤ 1 and Σ_{t=1}^T µ^t_ik ≤ Sik holds by
the definition of y^t_m from (10)"): for every feasible point `y` of the expected LP, every pair
`(i, k)` and every period, `0 ≤ μ^t_{ik} ≤ 1`, and `∑_t μ^t_{ik} ≤ S_{ik}`. -/
theorem mu_bounds {I K Q : Type} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    [Fintype Q] [DecidableEq Q] {T : ℕ} (P : Instance I K Q T) (hP : Valid P)
    (y : Q → Finset (I × K) → ℝ) (hy : LPFeasible P y) (i : I) (k : K) :
    (∀ t, 0 ≤ mu P y t i k ∧ mu P y t i k ≤ 1) ∧ ∑ t, mu P y t i k ≤ (P.S i k : ℝ) := by sorry

end MethodFulfillment
