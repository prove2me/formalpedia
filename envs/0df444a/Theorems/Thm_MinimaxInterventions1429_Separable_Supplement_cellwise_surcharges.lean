-- Prove2me | Theorems.Thm_MinimaxInterventions1429_Separable_Supplement_cellwise_surcharges
-- name    : MinimaxInterventions1429.Separable.Supplement.cellwise_surcharges
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:24:34.828845+00:00
-- url     : https://prove2.me/theorems/1cbf542f-2d3b-4345-a328-12a939077ff2
-- title:
--   Theorem C.2 — Cellwise surcharges
-- statement:
--   Let $m,k\ge2$, $0\le\beta<1$, $0\le\alpha\le1/8$, $T\ge3$ and $\eta=2^{-T}$. A numerical-mixture synopsis simultaneously accurate on the entire cellwise cube $[-5,5]^{m\times k}$ yields, by the literal deterministic postprocessing, an anchored real table with
--   $$\|\widehat L-(L-L_{11}\mathbf1)\|_\infty\le12\alpha+5\eta$$
--   with probability at least $1-\beta$. The program makes at most $m(k-1)T+m-1$ calls, every surcharge has norm at most $5$, and the output is measurable. No interaction assumption is imposed, and $\beta=0$ is included. This states the anchored entrywise guarantee rather than replacing it with a quotient-distance conclusion.
--
--   Differences from the source:
--   - encoding: m(k-1)T+m-1 numerical decoder calls and anchored infinity error → a numerical query program with a universal at-most budget and measurable anchored output; reason: the literal program makes exactly that many calls; at-most is the resource guarantee and no norm or probability is weakened
--   - encoding: m and k indexed from 1, with m,k >= 2 → Fin m and Fin k indexed from 0, with explicit nonzero instances and m,k >= 2; reason: source column 1 is Lean column 0; dimensions and closed-simplex boundary instances are preserved
-- source:
--   chaomeng chen, STOC 2027 submission #1429 (October 2026), Theorem C.2, printed p.29 (PDF p.31)

import Definitions.Def_MinimaxInterventions1429_Separable_Supplement_Numerical
set_option autoImplicit false
universe u_cellwise_surcharges

noncomputable section

namespace MinimaxInterventions1429.Separable.Supplement
open MeasureTheory

theorem cellwise_surcharges
    {m k : ℕ} [NeZero m] [NeZero k] (hm : 2 ≤ m) (hk : 2 ≤ k)
    (α β : ℝ) (hα : 0 ≤ α ∧ α ≤ 1/8) (hβ : 0 ≤ β ∧ β < 1)
    (T : ℕ) (hT : 3 ≤ T) :
    (cellwiseReconstruction m k α T).usesAtMost (m*(k-1)*T+m-1) ∧
    (cellwiseReconstruction m k α T).queriesSatisfy (fun B => entryNorm B ≤ 5) ∧
    ∀ (L : Table m k), InCube L → ∀ (S : Type u_cellwise_surcharges) [MeasurableSpace S]
      (syn : Synopsis S m k) (μ : Measure S) [IsProbabilityMeasure μ],
      Success μ β (AccurateOn syn.decode {B | entryNorm B ≤ 5} L α) →
      Measurable (cellwiseOutput syn.decode α T) ∧
      Success μ β (fun s => entryNorm
        (cellwiseOutput syn.decode α T s - (fun g h => L g h-L 0 0)) ≤ 12*α+5*eta T) := by sorry

end MinimaxInterventions1429.Separable.Supplement
