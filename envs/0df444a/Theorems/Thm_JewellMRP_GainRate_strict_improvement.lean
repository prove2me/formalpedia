-- Prove2me | Theorems.Thm_JewellMRP_GainRate_strict_improvement
-- name    : JewellMRP.GainRate.strict_improvement
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:26:28.342985+00:00
-- url     : https://prove2.me/theorems/e1cc23c5-f26d-486d-a8c1-9af5fcf976ad
-- title:
--   p. 955: a change of policy indicated by the test quantity strictly increases the gain rate, $g^{z_2} > g^{z_1}$
-- statement:
--   Let a Markov-renewal program be ergodic with positive mean sojourn times. Let $z_1$ be a stationary policy, $(g_1, v_1)$ a solution of its value-determination equations (13), and let $z_2$ be an improvement step of $z_1$ with respect to $v_1$: in each state $i$, $z_2(i)$ maximizes the test quantity
--   $$\frac{1}{\nu^z_i}\Big\{\rho^z_i + \sum_{j} p^z_{ij} v_{1,j} - v_{1,i}\Big\}$$
--   over the alternatives $z$, and $z_2(i) = z_1(i)$ when $z_1(i)$ already attains the maximum. If $z_2 \ne z_1$, then for all stationary probability vectors $\pi_1$, $\pi_2$ of the chains of $z_1$ and $z_2$,
--   $$g^{z_1} = \frac{\sum_i \pi_{1,i}\rho^{z_1(i)}_i}{\sum_k \pi_{1,k}\nu^{z_1(k)}_k} \;<\; \frac{\sum_i \pi_{2,i}\rho^{z_2(i)}_i}{\sum_k \pi_{2,k}\nu^{z_2(k)}_k} = g^{z_2}.$$
--
--   Since there are finitely many stationary policies, this strict monotonicity is what forces the algorithm of Fig. 2 to terminate.
-- source:
--   Jewell, Markov-Renewal Programming. II: Infinite Return Models, Example, Oper. Res. 11 (1963), p. 955 ("one shows that g^{z_2} > g^{z_1}"), with Fig. 2 (p. 956)

import Mathlib
import Definitions.Def_JewellMRP_GainRate_MRP
import Definitions.Def_JewellMRP_GainRate_PolicyIteration

namespace JewellMRP.GainRate
theorem strict_improvement {N : ℕ} [NeZero N] {α : Type*} (M : MRP N α)
    (hM : M.IsErgodic) (z₁ z₂ : Fin N → α) (g₁ : ℝ) (v₁ : Fin N → ℝ)
    (h₁ : M.SolvesValueDetermination z₁ g₁ v₁) (hstep : M.IsImprovementStep z₁ v₁ z₂)
    (hne : z₂ ≠ z₁) (π₁ π₂ : Fin N → ℝ)
    (hπ₁ : IsStationaryDist (M.policyMatrix z₁) π₁)
    (hπ₂ : IsStationaryDist (M.policyMatrix z₂) π₂) :
    M.gainRate z₁ π₁ < M.gainRate z₂ π₂ := by sorry
end JewellMRP.GainRate
