-- Prove2me | Theorems.Thm_FrictionInvest_Benefit_lemma_2
-- name    : FrictionInvest.Benefit.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:33:58.494365+00:00
-- url     : https://prove2.me/theorems/824042b5-9178-4f06-be01-a60544c375f6
-- title:
--   Lemma 2, p. 93 — marginal cost of external funds is convex and increasing
-- statement:
--   Let $\mathrm{MCE}(q)$ be the marginal cost of external funds for a firm with unit production cost $c>0$, capital $y\ge0$, and friction proportion $\gamma\in(0,1]$. On the feasible quantities, the curve is convex and nondecreasing; on the borrowing portion it is strictly increasing:
--   $$\mathrm{MCE}\text{ is convex and nondecreasing, and strictly increasing when }cq>y.$$
--   The result applies to the paper's investing and noninvesting firms by taking $(c,y)=(c_2,y_2)$ or $(c_1,y_1)$.
--
--   **Formalization Note** $\mathrm{MCE}=0$ at self-financed quantities, so strict increase is restricted to the borrowing region.
-- source:
--   Tanrisever, Joglekar, Erzurumlu & Lévesque, Managing capital market frictions via cost-reduction investments, M&SOM 23(1), 2021, p. 93 (PDF 6), Lemma 2

import Mathlib
import Definitions.Def_FrictionInvest_Benefit_Model

namespace FrictionInvest.Benefit

/-- Lemma 2, p. 93: the marginal financing-cost curve is convex and increasing. -/
theorem lemma_2 (P : Params) (hp : 0 < P.p) (ha : 0 < P.a)
    (γ c y : ℝ) (hγ : 0 < γ ∧ γ ≤ 1) (hc : 0 < c) (hy : 0 ≤ y) :
    ConvexOn ℝ {q : ℝ | Feasible P γ c y q} (mce P γ c y) ∧
    StrictMonoOn (mce P γ c y) {q : ℝ | Feasible P γ c y q ∧ y < c * q} ∧
    MonotoneOn (mce P γ c y) {q : ℝ | Feasible P γ c y q} := by sorry

end FrictionInvest.Benefit
