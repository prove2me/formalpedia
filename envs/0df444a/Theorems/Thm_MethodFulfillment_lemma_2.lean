-- Prove2me | Theorems.Thm_MethodFulfillment_lemma_2
-- name    : MethodFulfillment.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:15:37.383495+00:00
-- url     : https://prove2.me/theorems/691344d7-9579-4185-8184-89e51c7fef30
-- title:
--   Lemma 2 — a $\gamma$-conservative strategy gives ratio $1+(\kappa-1)(1-\gamma)$
-- statement:
--   Let $y$ be an optimal solution of the expected LP (6). If Algorithm 1, run with $y$, uses a $\gamma$-conservative method-acceptance strategy in step 2 of the online process, then its competitive ratio is at most $1+(\kappa-1)(1-\gamma)$:
--   $$\mathbb E[\mathrm{ALG}(D)]\le\big(1+(\kappa-1)(1-\gamma)\big)\,\mathbb E[\mathrm{OPT}(D)] .$$
--   Here $\kappa$ bounds the ratio between the cost of not fulfilling an order and the cost of any method.
--
--   The lemma reduces the competitive analysis of Algorithm 1 to the design of a strategy that accepts every drawn method with probability at least $\gamma$.
--
--   **Formalization Note** The ratio is multiplied out. The statement holds for every non-anticipating strategy and every real $\gamma$.
--
--   Differences from the source:
--   - generalization: a γ-conservative method-acceptance strategy (one that decides "based on the available inventories", p.13) → every non-anticipating strategy, without an inventory-feasibility requirement; reason: the cost bound does not use feasibility; feasible strategies are included
--   - generalization: γ (a probability level) → every real γ; reason: the bound is true for every real γ; the source's γ is included
--   - reading: decision rules π_t(h_t, m) on the history and the drawn method (Definition 3) → kernels on the history, the arriving order type and the drawn method; reason: in the paper a method determines its order type
--   - encoding: competitive ratio E[ALG(D)]/E[OPT(D)] at most B → E[ALG(D)] ≤ B · E[OPT(D)]; reason: cross-multiplied; equivalent when E[OPT(D)] > 0 and not vacuous at 0/0
--   - encoding: the online process with history-dependent, possibly randomized decision rules → an explicit law runProb on runs (arrival, drawn method, available set) with non-anticipating kernels; reason: same law; the run records every decision
--   - encoding: a dummy facility 0 with infinite inventory; the discard method m′(q) uses it for all items of q → a method is its set of real-facility pairs; the discard method is ∅; methods and costs are indexed by their order type; reason: Lean convention; the same instances
--   - encoding: periods t ∈ [T] = {1,…,T}; arrivals D_qt → 0-based Fin T (Lean t is the paper's t + 1); arrivals as Option Q, none = no arrival; reason: Lean convention; the same instances
--   - encoding: c_{m′(q)}/c_m ≤ κ → c q ∅ ≤ κ * c q m, with no positivity assumption on costs; reason: cross-multiplied; with c q m ≤ c q ∅ and κ > 1 it forces c ≥ 0, so it excludes only undefined cases
--   - generalization: not fulfilling costs more than any other method (p.7, "higher") → c q m ≤ c q ∅ (ties allowed); reason: p.36 assumes the discard method is the "largest"; allowing equality covers the strict case
--   - encoding: inventories Sik ≥ 0 → S_ik ∈ ℕ; reason: inventory is counted in units (p.15, "one unit")
-- source:
--   Amil, Makhdoumi & Wei, Multi-Item Order Fulfillment Revisited: LP Formulation and Prophet Inequality, manuscript (PDF sha256 197c13b9…), Lemma 2, p.14; proof pp.36–37

import Mathlib
import Definitions.Def_MethodFulfillment_Instance
import Definitions.Def_MethodFulfillment_Valid
import Definitions.Def_MethodFulfillment_expOPT
import Definitions.Def_MethodFulfillment_IsLPOpt
import Definitions.Def_MethodFulfillment_IsPolicy
import Definitions.Def_MethodFulfillment_expALG
import Definitions.Def_MethodFulfillment_IsConservative

namespace MethodFulfillment

/-- **Lemma 2** (Amil, Makhdoumi & Wei, manuscript, PDF sha256 197c13b9…, Lemma 2, p.14; proof
pp.36–37): if Algorithm 1, run with an optimal solution `y` of the expected LP (6), uses a
`γ`-conservative method-acceptance strategy `σ` in step 2, its competitive ratio is at most
`1 + (κ − 1)(1 − γ)`: `E[ALG(D)] ≤ (1 + (κ − 1)(1 − γ)) · E[OPT(D)]`.

**Formalization Note.** The ratio is cross-multiplied. Every non-anticipating strategy and every
real `γ` is admitted. -/
theorem lemma_2 {I K Q : Type} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    [Fintype Q] [DecidableEq Q] {T : ℕ} (P : Instance I K Q T) (hP : Valid P)
    (y : Q → Finset (I × K) → ℝ) (hy : IsLPOpt P y)
    (σ : Fin T → Run I K Q T → Option Q → Finset (I × K) → Finset (I × K) → ℝ)
    (hσ : IsPolicy σ) (γ : ℝ) (hγ : IsConservative P y σ γ) :
    expALG P y σ ≤ (1 + (P.κ - 1) * (1 - γ)) * expOPT P := by sorry

end MethodFulfillment
