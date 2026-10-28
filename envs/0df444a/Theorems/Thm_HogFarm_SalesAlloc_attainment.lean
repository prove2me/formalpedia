-- Prove2me | Theorems.Thm_HogFarm_SalesAlloc_attainment
-- name    : HogFarm.SalesAlloc.attainment
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T05:51:59.788365+00:00
-- url     : https://prove2.me/theorems/fd989d05-9d6e-4072-8113-28c652985578
-- title:
--   Proof of Proposition 1, Step 2 — four one-period allocations
-- statement:
--   Take a concave net holding value $G(Z)$ with forward holding margin at most $\max(p^C+c^P,p^2)$. For nonnegative stock and feasible decisions, the one-period objective is
--
--   $$J=p^C(y^2+(1-\alpha)y^1)+p^1(s^1-y^1-z^1)+p^2(s^2-y^2-z^2)-c^P(q-y^1-y^2)+G(z^1+z^2).$$
--
--   In each of Proposition 1's Cases 1(a), 1(b), 2(a), and 2(b), its explicit threshold action is feasible and maximizes $J$ over all feasible actions. This is the one-period attainment content of Step 2. **Formalization Note** Case 1(b) uses the stock remaining after contract allocation for holding; Case 2 reduces the regular-weight holding threshold by underweight holding. The false multi-period Case 2(c) is excluded.
-- source:
--   Kouvelis, Liu, Qiu & Turcic, Managing Operations of a Hog Farm Facing Volatile Markets, SSRN preprint 3912801 (March 6, 2023), pp. 42–45 (PDF 42–45), proof of Proposition 1, Step 2

import Mathlib
import Definitions.Def_HogFarm_SalesAlloc_Model

namespace HogFarm.SalesAlloc

/-- The four valid cases of Proposition 1's one-period Step 2, pp. 42–45. -/
theorem attainment (P : Prices) (q α s1 s2 : ℝ) (G : ℝ → ℝ)
    (hq : 0 < q) (hα0 : 0 < α) (hα1 : α < 1)
    (hp1 : 0 ≤ P.p1) (hp12 : P.p1 ≤ P.p2) (hpC : 0 ≤ P.pC)
    (hcP : 0 ≤ P.cP) (hs1 : 0 ≤ s1) (hs2 : 0 ≤ s2)
    (hG : ConcaveOn ℝ (Set.Ici 0) G)
    (hbound : ∀ Z : ℝ, 0 ≤ Z → MarginLE G (max (P.pC + P.cP) P.p2) Z) :
    let f1 := (1 - α) * P.pC + P.cP
    let f2 := P.pC + P.cP
    let zl1 := levelOf G (s1 + s2) f1
    let zb1 := levelOf G (s1 + s2) P.p1
    let Zb2 := levelOf G (s1 + s2) P.p2
    (f2 < P.p2 → f1 < P.p1 →
      OnePeriodOptimal P q α s1 s2 G 0 0 (min s1 zb1) 0) ∧
    (f2 < P.p2 → P.p1 ≤ f1 →
      let y1 := min (max (s1 - zl1) 0) q
      OnePeriodOptimal P q α s1 s2 G y1 0 (min (s1 - y1) zb1) 0) ∧
    (P.p2 ≤ f2 → f1 < P.p1 →
      let z1 := min s1 zb1
      OnePeriodOptimal P q α s1 s2 G 0 (min s2 q) z1
        (min (max (s2 - q) 0) (max (Zb2 - z1) 0))) ∧
    (P.p2 ≤ f2 → 0 ≤ f1 - P.p1 → f1 - P.p1 ≤ f2 - P.p2 →
      let y1 := min (max (s1 - zl1) 0) (max (q - s2) 0)
      let z1 := min (max (s1 - y1) 0) zb1
      OnePeriodOptimal P q α s1 s2 G y1 (min s2 q) z1
        (min (max (s2 - q) 0) (max (Zb2 - z1) 0))) := by sorry

end HogFarm.SalesAlloc
