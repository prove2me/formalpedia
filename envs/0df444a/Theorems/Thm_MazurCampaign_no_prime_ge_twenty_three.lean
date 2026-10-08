-- Prove2me | Theorems.Thm_MazurCampaign_no_prime_ge_twenty_three
-- name    : MazurCampaign.no_prime_ge_twenty_three
-- status  : Open
-- author  : @Xiang Huang
-- created : 2026-10-07T13:32:24.59931+00:00
-- url     : https://prove2.me/theorems/6f3af729-845e-43f4-8dbd-60d7c5d4a2fc
-- title:
--   No rational torsion point of prime order at least 23 on an elliptic curve over Q
-- statement:
--   Let $E$ be an elliptic curve over $\mathbb{Q}$ and let $p \ge 23$ be a prime. No rational torsion point of $E$ has order $p$.
-- source:
--   Case split of the mission leaf MazurCampaign.no_prime_ge_seventeen (Mazur's theorem for prime orders, B. Mazur, Modular curves and the Eisenstein ideal, Publ. Math. IHES 47 (1977); Rational isogenies of prime degree, Invent. Math. 44 (1978)). Split proposed by Xiang Huang so that p = 17 and p = 19 can be closed separately; proofs of those two cases exist in https://github.com/xiangyazi24/FLT (commit 51bbb4f191ad0d3753b87123635c100a638ae580, Apache-2.0).

import Mathlib
import Definitions.Def_MazurCampaign_group_constraints

theorem MazurCampaign.no_prime_ge_twenty_three
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∀ p : ℕ, p.Prime → 23 ≤ p →
      ∀ x : MazurCampaign.RationalTorsion E, addOrderOf x ≠ p := by sorry
