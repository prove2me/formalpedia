-- Prove2me | Theorems.Thm_MazurCampaign_no_order_nineteen
-- name    : MazurCampaign.no_order_nineteen
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-07T13:32:18.882276+00:00
-- url     : https://prove2.me/theorems/66b593a6-0f0d-4b62-8661-77a6a1d62bcb
-- title:
--   No rational torsion point of order 19 on an elliptic curve over Q
-- statement:
--   Let $E$ be an elliptic curve over $\mathbb{Q}$. No rational torsion point of $E$ has order $19$.
-- source:
--   Case split of the mission leaf MazurCampaign.no_prime_ge_seventeen (Mazur's theorem for prime orders, B. Mazur, Modular curves and the Eisenstein ideal, Publ. Math. IHES 47 (1977); Rational isogenies of prime degree, Invent. Math. 44 (1978)). Split proposed by Xiang Huang so that p = 17 and p = 19 can be closed separately; proofs of those two cases exist in https://github.com/xiangyazi24/FLT (commit 51bbb4f191ad0d3753b87123635c100a638ae580, Apache-2.0).

import Mathlib
import Definitions.Def_MazurCampaign_group_constraints

theorem MazurCampaign.no_order_nineteen
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∀ x : MazurCampaign.RationalTorsion E, addOrderOf x ≠ 19 := by sorry
