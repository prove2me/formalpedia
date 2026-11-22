-- Prove2me | Theorems.Thm_MultiwayGap2325_Main_Supplement_flow_limit_lower_bound
-- name    : MultiwayGap2325.Main.Supplement.flow_limit_lower_bound
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-22T22:55:33.292056+00:00
-- url     : https://prove2.me/theorems/2867fc3d-7a5d-4987-acc6-8d6d0c1843f9
-- title:
--   Theorem 3.4 — Conversion to the limiting CKR gap
-- statement:
--   For a valid flow instance with $L>0$, the CKR gap sequence has a real limit $g$ and
--   $$
--   g\ge \frac{B-R}{L}.
--   $$
--
--   For $B-R>0$, Theorem 3.4’s bound $\alpha\ge(B-R)/L$ applies to every random non-opposite cut of $\Delta_q$, so Lemma 2.2 supplies the conclusion. If $B-R\le0$, the same inequality follows because every finite-instance gap is at least one and the limit is positive.
--
--   **Formalization Note** This isolates the final limiting-gap clause of Theorem 3.4. The existence of the limit and the full eventual finite-instance witnesses are already packaged by the proved non-opposite reduction.
-- source:
--   Dimitar Chakarov, Yury Makarychev, STOC 2027 submission #697 (October 2026), conclusion of the proof of Theorem 3.4, p.8; Lemma 2.2, p.4.

import Definitions.Def_MultiwayGap2325_Main_Supplement_FluxJumps

open MeasureTheory Filter
open MultiwayGap2325.Main MultiwayGap2325.Main.Supplement
open scoped BigOperators ENNReal

/-- The last conclusion of Theorem 3.4, p.8. If the flow value is positive this
is Lemma 2.2; in the nonpositive case it uses positivity of the limit. -/
theorem MultiwayGap2325.Main.Supplement.flow_limit_lower_bound
    (q : ℕ) (hq : 2 ≤ q) (T : ℝ)
    (hT0 : 1 / 2 < T) (hT1 : T < 1) (D : FlowData q)
    (hD : IsFlowInstance T D) (hL : 0 < totalL T D.weighting) :
    ∃ g : ℝ, Tendsto gapSequence atTop (nhds g) ∧
      (totalB T D.weighting - totalR T D) / totalL T D.weighting ≤ g := by sorry
