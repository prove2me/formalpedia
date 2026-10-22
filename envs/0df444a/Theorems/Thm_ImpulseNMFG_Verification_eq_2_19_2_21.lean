-- Prove2me | Theorems.Thm_ImpulseNMFG_Verification_eq_2_19_2_21
-- name    : ImpulseNMFG.Verification.eq_2_19_2_21
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:15:29.234989+00:00
-- url     : https://prove2.me/theorems/11c0d401-a1da-4dba-905c-01cbbc7a8f37
-- title:
--   Theorem 2.12, proof, (2.19)–(2.21), pp. 11–12 — pointwise QVI cost bounds
-- statement:
--   Let $V$ satisfy the QVI system and let each $\xi_i$ be the unique minimizing impulse. On the common waiting region away from $\partial D_i$, the generator term is bounded below by the negative running cost. At a point $y\in S$, the value is at most the own-intervention value, which is no larger than the cost of any allowed impulse $z\in Z_i$. When another player $j\ne i$ acts at a point where its own intervention gap is zero, player $i$'s value equals the cross-intervention value:
--   $$
--   \mathcal LV_i(y)-\rho_iV_i(y)\ge -f_i(y),\quad
--   V_i(y)\le\mathcal M_iV_i(y)\le V_i(\Gamma^i(y,z))+\phi_i(y,z),\quad
--   V_i(y)=\mathcal H_{i,j}V_i(y).
--   $$
--   These elementary consequences are the three comparisons used after the localized Itô identity in Step 1.
--
--   **Formalization Note** The displayed inequalities are pointwise versions of (2.19)–(2.21), stated on the domains where the paper applies them. The first domain excludes $\partial D_i$, where the generator of $V_i$ need not exist. The last equality applies only when $\mathcal M_jV_j(y)=V_j(y)$.
-- source:
--   Basei, Cao, Guo, Nonzero-sum stochastic games and mean-field games with impulse controls, arXiv:1901.08085v4, pp. 11–12, Theorem 2.12, proof, (2.19)–(2.21)

import Mathlib
import Definitions.Def_ImpulseNMFG_Verification_Game
import Definitions.Def_ImpulseNMFG_Verification_QVI
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
open ImpulseGames.Verification (State IsBrownianBasis)

namespace ImpulseNMFG.Verification
noncomputable section
/-- Basei, Cao, Guo, Nonzero-sum stochastic games and mean-field games with impulse controls,
arXiv:1901.08085v4, pp. 11–12, Theorem 2.12, proof, (2.19)–(2.21).
These are pointwise consequences of the QVI and unique-argmin condition. -/
theorem eq_2_19_2_21 {N d M : ℕ} [NeZero N] (G : Game N d M)
    (V : Fin N → State d → ℝ) (ξ : (i : Fin N) → State d → G.Imp i)
    (h210 : ∀ i, IsUniqueMinimizer G V ξ i)
    (hi : ∀ i, SolvesQVI G V ξ i) :
    (∀ i, ∀ y ∈ commonWait G V ξ i \ frontier (waitRegion G V ξ i),
      -G.f i y ≤ ImpulseGames.Verification.generator G.b G.σ (V i) y -
        G.ρ i * V i y) ∧
    (∀ i, ∀ y ∈ G.S, ∀ z ∈ G.Z i,
      V i y ≤ ownOp G V ξ i y ∧
      ownOp G V ξ i y ≤ V i (G.Γ i y z) + G.φ i y z) ∧
    (∀ i j, i ≠ j → ∀ y ∈ G.S,
      ownOp G V ξ j y - V j y = 0 →
      V i y = crossOp G V ξ i j y) := by sorry
end
end ImpulseNMFG.Verification
