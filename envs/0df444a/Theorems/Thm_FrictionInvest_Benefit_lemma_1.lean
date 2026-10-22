-- Prove2me | Theorems.Thm_FrictionInvest_Benefit_lemma_1
-- name    : FrictionInvest.Benefit.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:33:57.766565+00:00
-- url     : https://prove2.me/theorems/37f35562-ac48-4466-aded-c24bc2ed2239
-- title:
--   Lemma 1, p. 93 — expected bankruptcy cost is increasing and strictly convex
-- statement:
--   For a firm that borrows to produce quantity $q$ and satisfies the two lending conditions, let $K(q)$ be its expected bankruptcy cost under $\xi\sim U[0,a]$ and a positive friction proportion $\gamma$. Then
--   $$K(q)>0,\qquad K'(q)>0,\qquad K''(q)>0.$$
--   Thus borrowing raises the expected bankruptcy cost at an increasing rate, a property used in the equilibrium analysis.
--
--   **Formalization Note** The open borrowing-region and $\gamma>0$ guards are necessary: bankruptcy cost is zero on the self-financed branch or when $\gamma=0$.
-- source:
--   Tanrisever, Joglekar, Erzurumlu & Lévesque, Managing capital market frictions via cost-reduction investments, M&SOM 23(1), 2021, p. 93 (PDF 6), Lemma 1

import Mathlib
import Definitions.Def_FrictionInvest_Benefit_Model

namespace FrictionInvest.Benefit

/-- Lemma 1, p. 93: positive, increasing, strictly convex bankruptcy cost in the borrowing region. -/
theorem lemma_1 (P : Params) (hp : 0 < P.p) (ha : 0 < P.a)
    (γ c y q : ℝ) (hγ : 0 < γ ∧ γ ≤ 1) (hc : 0 < c) (hy : 0 ≤ y)
    (hq : 0 ≤ q) (hborrow : y < c * q)
    (hbound : 2 * (1 + γ) * (c * q - y) < P.a * P.p)
    (hloan : faceValue P γ c y q < q * P.p) :
    0 < bankCost P γ c y q ∧
      0 < deriv (bankCost P γ c y) q ∧
      0 < deriv (deriv (bankCost P γ c y)) q := by sorry

end FrictionInvest.Benefit
