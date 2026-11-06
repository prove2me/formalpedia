-- Prove2me | Theorems.Thm_MethodFulfillment_never_over_consumes
-- name    : MethodFulfillment.never_over_consumes
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:14:56.85423+00:00
-- url     : https://prove2.me/theorems/72c9327f-16e6-4fc1-a50a-914a76c67895
-- title:
--   p.17 — the magicians never use more than $S_{ik}$ units
-- statement:
--   Run Algorithm 1 with a feasible point $y$ of the expected LP and Algorithm 2 in step 2, where each magician $(i,k)$ is given inputs $\nu^t_{ik}$ with $\mu^t_{ik}\le\nu^t_{ik}\le1$ and $\sum_t\nu^t_{ik}\le S_{ik}$ (the guarantee of Definition 4; Algorithm 2's own inputs $\nu=\mu$ satisfy it). Then on every run of positive probability, for every period $t$ up to the end of the horizon and every pair $(i,k)$,
--   $$W^t_{ik}\le S_{ik} :$$
--   no pair ever uses more units than its inventory. The magicians' coins may have any joint law with the right marginals.
--
--   Algorithm 2 never checks the remaining stock, so this is what makes Algorithm 1 with Algorithm 2 a feasible fulfillment policy.
--
--   Differences from the source:
--   - generalization: y obtained in the offline process (an optimal solution of (6)) → every LP-feasible y; reason: the argument uses only feasibility
--   - reading: "magician (i,k) never requires more than Sik inventory" → on every run of positive probability, usage ≤ S_ik at every t ≤ T; reason: "never" read as almost surely, for every period
--   - generalization: Algorithm 2's magicians, each deciding with its own probability → every joint law of the magicians' decisions with these marginals (IsAlg2Rule); reason: the paper does not fix the joint law and its argument does not use one; independent coins are one such law
--   - generalization: Definition 4: the magician starts with S_ik > 0 units (with S_ik < T) → S_ik < T not assumed; reason: the recursion needs no such condition; the case S_ik < T is included
--   - encoding: the online process with history-dependent, possibly randomized decision rules → an explicit law runProb on runs (arrival, drawn method, available set) with non-anticipating kernels; reason: same law; the run records every decision
--   - encoding: a dummy facility 0 with infinite inventory; the discard method m′(q) uses it for all items of q → a method is its set of real-facility pairs; the discard method is ∅; methods and costs are indexed by their order type; reason: Lean convention; the same instances
--   - encoding: periods t ∈ [T] = {1,…,T}; arrivals D_qt → 0-based Fin T (Lean t is the paper's t + 1); arrivals as Option Q, none = no arrival; reason: Lean convention; the same instances
--   - generalization: not fulfilling costs more than any other method (p.7, "higher") → c q m ≤ c q ∅ (ties allowed); reason: p.36 assumes the discard method is the "largest"; allowing equality covers the strict case
--   - encoding: c_{m′(q)}/c_m ≤ κ → c q ∅ ≤ κ * c q m, with no positivity assumption on costs; reason: cross-multiplied; with c q m ≤ c q ∅ and κ > 1 it forces c ≥ 0, so it excludes only undefined cases
--   - encoding: inventories Sik ≥ 0 → S_ik ∈ ℕ; reason: inventory is counted in units (p.15, "one unit")
-- source:
--   Amil, Makhdoumi & Wei, Multi-Item Order Fulfillment Revisited: LP Formulation and Prophet Inequality, manuscript (PDF sha256 197c13b9…), p.17; Appendix D, p.59

import Mathlib
import Definitions.Def_MethodFulfillment_Instance
import Definitions.Def_MethodFulfillment_Valid
import Definitions.Def_MethodFulfillment_LPFeasible
import Definitions.Def_MethodFulfillment_runProb
import Definitions.Def_MethodFulfillment_usage
import Definitions.Def_MethodFulfillment_mu
import Definitions.Def_MethodFulfillment_IsAlg2Rule

namespace MethodFulfillment

/-- **The magicians never over-consume** (Amil, Makhdoumi & Wei, manuscript, PDF sha256 197c13b9…,
Appendix D, p.59, and p.17: "magician (i,k) never requires more than Sik inventory"): under
Algorithm 1 with Algorithm 2, when each magician `(i, k)` is given inputs `ν^t_{ik} ∈ [μ^t_{ik}, 1]`
(upper bounds on the consumption probabilities (12)) with `∑_t ν^t_{ik} ≤ S_{ik}` (Definition 4's
guarantee; Algorithm 2's own inputs `ν = μ` satisfy it), then on every run of positive probability,
at every time `t ≤ T`, at most `S_{ik}` units of every pair `(i, k)` have been used. So the policy is
a feasible fulfillment policy, although Algorithm 2 never checks the stock. -/
theorem never_over_consumes {I K Q : Type} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    [Fintype Q] [DecidableEq Q] {T : ℕ} (P : Instance I K Q T) (hP : Valid P)
    (y : Q → Finset (I × K) → ℝ) (hy : LPFeasible P y)
    (ν : I → K → ℕ → ℝ) (hν : ∀ (i : I) (k : K) t, mu' P y i k t ≤ ν i k t ∧ ν i k t ≤ 1)
    (hνS : ∀ (i : I) (k : K), ∑ t ∈ Finset.range T, ν i k t ≤ (P.S i k : ℝ))
    (ρ : Fin T → Run I K Q T → Finset (I × K) → ℝ) (hρ : IsAlg2Rule P ν ρ) :
    ∀ r, 0 < runProb P y (alg2Policy ρ) r → ∀ t ≤ T, ∀ (i : I) (k : K),
      usage r t i k ≤ P.S i k := by sorry

end MethodFulfillment
