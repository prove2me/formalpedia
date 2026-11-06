-- Prove2me | Theorems.Thm_MethodFulfillment_lemma_1
-- name    : MethodFulfillment.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:13:00.166918+00:00
-- url     : https://prove2.me/theorems/8c96ebbb-e77c-460c-8364-3dbf129b2e74
-- title:
--   Lemma 1 — $\mathrm{OPT}^E\le\mathbb E[\mathrm{OPT}(D)]$
-- statement:
--   For every valid fulfillment instance, the optimal value of the expected LP (6)–(9) is at most the expected offline optimum of the integer program (1)–(4):
--   $$\mathrm{OPT}^E\le\mathbb E[\mathrm{OPT}(D)] .$$
--   Equivalently, some feasible point $x$ of the expected LP satisfies $\sum_q\sum_{m\in M(q)}c_m x_m\le\mathbb E[\mathrm{OPT}(D)]$.
--
--   The expected LP is therefore a lower bound on the benchmark, which is how the competitive ratio of Algorithm 1 is controlled.
--
--   **Formalization Note** The statement is written as the existence of a feasible LP point with objective at most $\mathbb E[\mathrm{OPT}(D)]$; since the LP attains its minimum $\mathrm{OPT}^E$, this is the paper's inequality.
--
--   Differences from the source:
--   - encoding: OPT^E ≤ E[OPT(D)] → ∃ x, LPFeasible P x ∧ lpObj P x ≤ expOPT P; reason: OPT^E is the attained minimum of (6), so the two are equivalent
--   - encoding: a dummy facility 0 with infinite inventory; the discard method m′(q) uses it for all items of q → a method is its set of real-facility pairs; the discard method is ∅; methods and costs are indexed by their order type; reason: Lean convention; the same instances
--   - encoding: periods t ∈ [T] = {1,…,T}; arrivals D_qt → 0-based Fin T (Lean t is the paper's t + 1); arrivals as Option Q, none = no arrival; reason: Lean convention; the same instances
--   - encoding: c_{m′(q)}/c_m ≤ κ → c q ∅ ≤ κ * c q m, with no positivity assumption on costs; reason: cross-multiplied; with c q m ≤ c q ∅ and κ > 1 it forces c ≥ 0, so it excludes only undefined cases
--   - generalization: not fulfilling costs more than any other method (p.7, "higher") → c q m ≤ c q ∅ (ties allowed); reason: p.36 assumes the discard method is the "largest"; allowing equality covers the strict case
--   - encoding: inventories Sik ≥ 0 → S_ik ∈ ℕ; reason: inventory is counted in units (p.15, "one unit")
-- source:
--   Amil, Makhdoumi & Wei, Multi-Item Order Fulfillment Revisited: LP Formulation and Prophet Inequality, manuscript (PDF sha256 197c13b9…), Lemma 1, p.12, (11); proof pp.35–36

import Mathlib
import Definitions.Def_MethodFulfillment_Instance
import Definitions.Def_MethodFulfillment_Valid
import Definitions.Def_MethodFulfillment_expOPT
import Definitions.Def_MethodFulfillment_LPFeasible
import Definitions.Def_MethodFulfillment_lpObj

namespace MethodFulfillment

/-- **Lemma 1** (Amil, Makhdoumi & Wei, manuscript, PDF sha256 197c13b9…, Lemma 1, p.12, (11)):
the optimal value of the expected LP (6) is at most the expected offline optimum,
`OPT^E ≤ E[OPT(D)]`.

**Formalization Note.** `OPT^E` is the minimum of (6); the statement "some feasible point of (6)
has objective at most `E[OPT(D)]`" is equivalent to `OPT^E ≤ E[OPT(D)]`. -/
theorem lemma_1 {I K Q : Type} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    [Fintype Q] [DecidableEq Q] {T : ℕ} (P : Instance I K Q T) (hP : Valid P) :
    ∃ x, LPFeasible P x ∧ lpObj P x ≤ expOPT P := by sorry

end MethodFulfillment
