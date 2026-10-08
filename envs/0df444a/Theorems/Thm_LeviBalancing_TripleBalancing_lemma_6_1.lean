-- Prove2me | Theorems.Thm_LeviBalancing_TripleBalancing_lemma_6_1
-- name    : LeviBalancing.TripleBalancing.lemma_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T19:22:21.270259+00:00
-- url     : https://prove2.me/theorems/ef940024-4a15-4905-9c0f-71c58f737a68
-- title:
--   Lemma 6.1 — every feasible policy costs at least $K\cdot E[N]$
-- statement:
--   Let TB be the triple-balancing policy for a stochastic lot-sizing model with (arbitrarily correlated) demand and conditional demand law $I$, and let $N$ be the number of orders TB places. Then every feasible policy $P$ satisfies
--   $$K\cdot E[N]\le E[\mathcal C(P)].$$
--
--   The paper states this for an optimal policy OPT; its proof uses only that OPT is feasible, and the statement for every feasible $P$ gives the paper's whenever an optimal policy exists. It is the lower bound half of the analysis of TB.
--
--   **Formalization Note** Both sides are in $[0,\infty]$: $E[N]$ and $E[\mathcal C(P)]$ are lower Lebesgue integrals.
-- source:
--   Levi, Pál, Roundy & Shmoys, Approximation Algorithms for Stochastic Inventory Control Models, Math. Oper. Res. 32(2):284–302 (2007), DOI 10.1287/moor.1060.0205, p. 300 (PDF 17), Lemma 6.1

import Mathlib
import Definitions.Def_LeviBalancing_TripleBalancing_Model
import Definitions.Def_LeviBalancing_TripleBalancing_Policy
import Definitions.Def_LeviBalancing_TripleBalancing_TBPolicy

open MeasureTheory ProbabilityTheory

namespace LeviBalancing.TripleBalancing

/-- Lemma 6.1 (p. 300), stated for every feasible policy `P` in place of an optimal policy:
`E[𝒞(P)] ≥ K · E[N]`, where `N` is the number of orders of the triple-balancing policy. -/
theorem lemma_6_1 {Ω : Type*} [MeasurableSpace Ω] (M : LotSizingModel Ω)
    (I : ℕ → Kernel Ω (ℕ → ℝ)) (hI : M.IsCondDemandLaw I)
    (TB : ℕ → Ω → ℝ) (hTB : IsTripleBalancing M I TB)
    (P : ℕ → Ω → ℝ) (hP : IsFeasiblePolicy M P) :
    ENNReal.ofReal M.K * ∫⁻ ω, (numOrders M TB ω : ENNReal) ∂M.μ ≤ expectedCost M P := by sorry

end LeviBalancing.TripleBalancing
