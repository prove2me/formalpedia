-- Prove2me | Theorems.Thm_LeviBalancing_TripleBalancing_lemma_6_2
-- name    : LeviBalancing.TripleBalancing.lemma_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T19:22:29.320879+00:00
-- url     : https://prove2.me/theorems/c528d78a-c78f-45c6-98e7-0b99f3e6576f
-- title:
--   Lemma 6.2 — $E[\mathcal C(TB)] \le E[\mathcal C(P)] + 2K\cdot E[N]$
-- statement:
--   Let TB be the triple-balancing policy for a stochastic lot-sizing model with conditional demand law $I$, and let $N$ be the number of orders TB places. Then every feasible policy $P$ satisfies
--   $$E[\mathcal C(TB)]\le E[\mathcal C(P)]+2K\cdot E[N].$$
--
--   The paper writes $E[\mathcal C(TB)-\mathcal C(OPT)]\le 2K\cdot E[N]$ for an optimal policy OPT. The additive form is the same inequality whenever the expectations are finite, and it remains meaningful when $E[\mathcal C(P)]=\infty$; the proof uses only the feasibility of OPT. Together with Lemma 6.1 it gives Theorem 6.1.
--
--   **Formalization Note** All quantities are in $[0,\infty]$ (lower Lebesgue integrals).
-- source:
--   Levi, Pál, Roundy & Shmoys, Approximation Algorithms for Stochastic Inventory Control Models, Math. Oper. Res. 32(2):284–302 (2007), DOI 10.1287/moor.1060.0205, p. 300 (PDF 17), Lemma 6.2

import Mathlib
import Definitions.Def_LeviBalancing_TripleBalancing_Model
import Definitions.Def_LeviBalancing_TripleBalancing_Policy
import Definitions.Def_LeviBalancing_TripleBalancing_TBPolicy

open MeasureTheory ProbabilityTheory

namespace LeviBalancing.TripleBalancing

/-- Lemma 6.2 (p. 300), stated for every feasible policy `P` in place of an optimal policy and in
additive form: `E[𝒞(TB)] ≤ E[𝒞(P)] + 2K · E[N]`. -/
theorem lemma_6_2 {Ω : Type*} [MeasurableSpace Ω] (M : LotSizingModel Ω)
    (I : ℕ → Kernel Ω (ℕ → ℝ)) (hI : M.IsCondDemandLaw I)
    (TB : ℕ → Ω → ℝ) (hTB : IsTripleBalancing M I TB)
    (P : ℕ → Ω → ℝ) (hP : IsFeasiblePolicy M P) :
    expectedCost M TB ≤
      expectedCost M P + 2 * ENNReal.ofReal M.K * ∫⁻ ω, (numOrders M TB ω : ENNReal) ∂M.μ := by sorry

end LeviBalancing.TripleBalancing
