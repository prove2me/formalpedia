-- Prove2me | Theorems.Thm_HartSchmeidler_Finite_product_strategy_payoff_zero
-- name    : HartSchmeidler.Finite.product_strategy_payoff_zero
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:53:01.79697+00:00
-- url     : https://prove2.me/theorems/176dbabc-a71b-489b-9113-6d5d654e31dc
-- title:
--   Proof of Theorem 1 — product strategy earns zero
-- statement:
--   Let $y$ be a lottery over all triples $(i,r^i,t^i)$ in the auxiliary game. Suppose that, for each player $i$, $x^i$ is a probability vector on $S^i$ satisfying equation (2) for the nonnegative slice $y^i(r^i,t^i)=y(i,r^i,t^i)$ and every $s^{-i}$. Set $x(s)=\prod_{j\in N}x^j(s^j)$. Then
--
--   $$
--   x\in\Delta(S),\qquad
--   \sum_{s\in S}\sum_c x(s)y(c)A(s,c)=0.
--   $$
--
--   This is the product-strategy calculation closing the nonnegative-response condition in the proof of Theorem 1.
--
--   **Formalization Note** Each $x^i$ is required to be a lottery, and the $y^i$ are slices of one global lottery. The calculation uses the exact auxiliary payment appearing in the correspondence milestone.
-- source:
--   Hart and Schmeidler, Existence of Correlated Equilibria, Math. Oper. Res. 14 (1989), p. 20, proof of Theorem 1 (‘Define x(r)’ through ‘which equals zero by (2)’); https://doi.org/10.1287/moor.14.1.18

import Definitions.Def_HartSchmeidler_Finite_Game

namespace HartSchmeidler.Finite

open Finset

/-- Proof of Theorem 1, p. 20: the product of the playerwise lotteries is
a mixed strategy of player I, and equation (2) makes its payoff zero. -/
theorem product_strategy_payoff_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ j, Fintype (S j)] [∀ j, DecidableEq (S j)]
    [∀ j, Nonempty (S j)] (h : ι → (∀ j, S j) → ℝ)
    (y : Deviation S → ℝ) (hy : AGT.IsLottery y)
    (x : ∀ i, S i → ℝ) (hx : ∀ i, AGT.IsLottery (x i))
    (hbalance : ∀ (i : ι) (s : ∀ j, S j),
      ∑ r : S i, x i r * ∑ t : S i, y ⟨i, (r, t)⟩ *
        (h i (Function.update s i r) - h i (Function.update s i t)) = 0) :
    AGT.IsLottery (fun r : ∀ j, S j => ∏ j, x j (r j)) ∧
      (∑ r, ∑ c, (∏ j, x j (r j)) * y c * auxPayoff h r c) = 0 := by sorry

end HartSchmeidler.Finite
