-- Prove2me | Theorems.Thm_HogFarm_SalesAlloc_lemma_2_1
-- name    : HogFarm.SalesAlloc.lemma_2_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T05:52:00.766988+00:00
-- url     : https://prove2.me/theorems/da557141-d97f-45a8-a6a8-f7fbe45f8470
-- title:
--   Lemma 2 (1), corrected under A* — no regular-weight crossing
-- statement:
--   Write $m_t=\max(p^C_t+c^P_t,p^2_t)$. Under the corrected no-arbitrage bound A*, every forward increment of net holding value satisfies
--
--   $$G_t(Z+\delta)-G_t(Z)\le m_t\delta\qquad(Z\ge0,\ \delta>0).$$
--
--   If $p^2_t\le p^C_t+c^P_t$, the regular-weight fulfillment break-even level is zero. This is the no-crossing assertion used in the policy theorem. **Formalization Note** A* is added because Assumption 1 alone does not control future penalties; a two-period counterexample gives the printed policy value $-80$ against $8$ from holding. The page's "for any prices" is also narrowed to $p^2_t\le p^C_t+c^P_t$: under A* alone, with $p^2_t>p^C_t+c^P_t$ the holding margin may exceed the regular-weight fulfillment margin (e.g. $p^C=c^P=c^H=0$, $p^2_t=p^2_{t+1}=100$, $\beta=1$), so $\underline z^2_t>0$ there; in Case 1 of Proposition 1 regular-weight hogs never go to the contract, so this level is not used.
-- source:
--   Kouvelis, Liu, Qiu & Turcic, Managing Operations of a Hog Farm Facing Volatile Markets, SSRN preprint 3912801 (March 6, 2023), p. 16 (PDF 16), Lemma 2(1); p. 39 (PDF 39), proof

import Mathlib
import Definitions.Def_HogFarm_SalesAlloc_Model

namespace HogFarm.SalesAlloc

/-- Lemma 2(1), p. 16, corrected by A*. -/
theorem lemma_2_1 {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω)
    (hS : M.Standing) (hA : M.AStar)
    (t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ M.T) (ω : Ω) :
    let P := M.price t ω
    let G := holdGain M t ω
    (∀ Z : ℝ, 0 ≤ Z → MarginLE G (max (P.pC + P.cP) P.p2) Z) ∧
    (P.p2 ≤ P.pC + P.cP → breakEvenOf G (P.pC + P.cP) = 0) := by sorry

end HogFarm.SalesAlloc
