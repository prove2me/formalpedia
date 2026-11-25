-- Prove2me | Theorems.Thm_IntConeFPT_counted_grid
-- name    : IntConeFPT.counted_grid
-- status  : Proved
-- author  : @ohnesorgefelix
-- created : 2026-11-25T11:38:32.233306+00:00
-- url     : https://prove2.me/theorems/161fee20-9138-4d31-a9da-9fa7537b3eb0
-- title:
--   Explicit polynomial bit bound for the counted objective grid
-- statement:
--   Let $L$ be the length of the counted input and $q$ the product of the reduced denominators of its cost coefficients. Then $0<q\le2^L$. Every feasible objective under the total count limit $N$ is $z/q$ with $|z|\le2^{L^2+4L}$. Thus searching integer budgets on this interval needs only polynomially many bits, even if the count itself is exponentially large.
-- source:
--   Jansen–Ohnesorge–Schumacher, A Constructive FPT Algorithm for Integer Cone Optimization with Convex Costs, https://arxiv.org/abs/2609.31328, §3.5, proof of Proposition 14, pp.16–17 (exact budget search); explicit estimates for the published encodings.

import Definitions.Def_IntConeFPT_Problem
open IntConeFPT OnlineCRS.Combine

theorem IntConeFPT.counted_grid (I : Instance) (hI : I.Valid) (N : ℕ) :
    let L := (encInstance I ++ encNat N ++ [3]).length
    let q := ∏ t, ∏ j, (I.coeff t j).den
    0 < q ∧ q ≤ 2^L ∧ ∀ μ : Mult I, I.FeasibleN N μ →
      ∃ z : ℤ, (q : ℝ) * I.cost μ = z ∧ z.natAbs ≤ 2^(L^2+4*L) := by sorry
