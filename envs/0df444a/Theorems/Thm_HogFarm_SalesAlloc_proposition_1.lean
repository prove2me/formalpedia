-- Prove2me | Theorems.Thm_HogFarm_SalesAlloc_proposition_1
-- name    : HogFarm.SalesAlloc.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T05:52:00.096609+00:00
-- url     : https://prove2.me/theorems/34a70dd7-6fc8-4213-bf9f-ebf2afc9e37d
-- title:
--   Proposition 1, Cases 1(a)–2(b), p. 17 (corrected) — optimal threshold allocation
-- statement:
--   For every period $1\le t\le t_M$, information state, and nonnegative stock, set $f_1=(1-\alpha)p^C_t+c^P_t$ and $f_2=p^C_t+c^P_t$. The explicit actions of Cases 1(a), 1(b), 2(a), and 2(b) in the formal statement are feasible and attain the Bellman value in their respective price regimes:
--
--   $$\begin{array}{ll}1(a):&f_2<p^2_t,\ f_1<p^1_t;\\1(b):&f_2<p^2_t,\ p^1_t\le f_1;\\2(a):&p^2_t\le f_2,\ f_1<p^1_t;\\2(b):&p^2_t\le f_2,\ 0\le f_1-p^1_t\le f_2-p^2_t.\end{array}$$
--
--   Each threshold is computed from the net holding value and current stock. Thus optimality concerns the paper's actual dynamic program. **Formalization Note** Assumption 1 is retained and A* is added to control future penalties. Case 1(b) holding and the Case 2 regular-weight threshold are corrected. The printed Case 2(c) is excluded: in a two-period example satisfying Assumption 1 and A*, its action yields $87$ while another yields $103$. Bounded measurable nonnegative data, $0<\beta\le1$, and $q>0$ are disclosed model assumptions.
-- source:
--   Kouvelis, Liu, Qiu & Turcic, Managing Operations of a Hog Farm Facing Volatile Markets, SSRN preprint 3912801 (March 6, 2023), p. 17 (PDF 17), Proposition 1, Cases 1(a)–2(b); pp. 42–45 (PDF 42–45), proof

import Mathlib
import Definitions.Def_HogFarm_SalesAlloc_Model

namespace HogFarm.SalesAlloc

/-- Proposition 1, p. 17, Cases 1(a)–2(b), with the corrections recorded
in the mission description. The printed Case 2(c) is excluded. -/
theorem proposition_1 {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω)
    (hS : M.Standing) (hA1 : M.Assumption1) (hA : M.AStar)
    (t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ M.T) (ω : Ω)
    (s1 s2 : ℝ) (hs1 : 0 ≤ s1) (hs2 : 0 ≤ s2) :
    let P := M.price t ω
    let f1 := (1 - M.α) * P.pC + P.cP
    let f2 := P.pC + P.cP
    let G := holdGain M t ω
    let zl1 := levelOf G (s1 + s2) f1
    let zb1 := levelOf G (s1 + s2) P.p1
    let Zb2 := levelOf G (s1 + s2) P.p2
    (f2 < P.p2 → f1 < P.p1 →
      IsOptimal M t ω s1 s2 0 0 (min s1 zb1) 0) ∧
    (f2 < P.p2 → P.p1 ≤ f1 →
      let y1 := min (max (s1 - zl1) 0) M.q
      IsOptimal M t ω s1 s2 y1 0 (min (s1 - y1) zb1) 0) ∧
    (P.p2 ≤ f2 → f1 < P.p1 →
      let z1 := min s1 zb1
      IsOptimal M t ω s1 s2 0 (min s2 M.q) z1
        (min (max (s2 - M.q) 0) (max (Zb2 - z1) 0))) ∧
    (P.p2 ≤ f2 → 0 ≤ f1 - P.p1 → f1 - P.p1 ≤ f2 - P.p2 →
      let y1 := min (max (s1 - zl1) 0) (max (M.q - s2) 0)
      let z1 := min (max (s1 - y1) 0) zb1
      IsOptimal M t ω s1 s2 y1 (min s2 M.q) z1
        (min (max (s2 - M.q) 0) (max (Zb2 - z1) 0))) := by sorry

end HogFarm.SalesAlloc
