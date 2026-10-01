-- Prove2me | Theorems.Thm_JewellMRP_InfiniteStep_limit_bias_equation
-- name    : JewellMRP.InfiniteStep.limit_bias_equation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:33:08.254485+00:00
-- url     : https://prove2.me/theorems/1c27a599-87f3-4ebb-86d5-055cd8548fac
-- title:
--   Eq. (4) — the limiting biases satisfy $W_i + G = \rho_i + \sum_j p_{ij} W_j$
-- statement:
--   Let $P$ be an irreducible row-stochastic matrix on a nonempty finite state set with stationary probability vector $\pi$, $\Pi$ the matrix all of whose rows equal $\pi$, $Z = (I - P + \Pi)^{-1}$, $\rho$ the one-step rewards, $G = \sum_i \pi_i\rho_i$, and $V(0)$ any terminal-reward vector. Define the limiting bias vector
--   $$W = (Z - \Pi)\rho + \Pi V(0).$$
--   Then for every state $i$
--   $$W_i + G = \rho_i + \sum_{j} p_{ij} W_j .$$
--
--   These are the relative-value equations (4) of the paper, which the policy-improvement algorithm solves instead of computing $\Pi$ and $Z$.
--
--   **Formalization Note** The paper derives (4) by substituting (A 5) into (I 16); (A 5) is used here in its corrected form $W = (Z-\Pi)\rho + \Pi V(0)$ (see the goal theorem). With the printed $W = (Z-\Pi)\rho + V(0)$, equation (4) fails unless $(I - P)V(0) = 0$.
-- source:
--   Jewell, Markov-Renewal Programming. II: Infinite Return Models, Example, Oper. Res. 11 (1963), p. 952, Eq. (4)

import Mathlib
import Definitions.Def_JewellMRP_InfiniteStep_Model

open Matrix Filter Topology

namespace JewellMRP.InfiniteStep

theorem limit_bias_equation {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (P : Matrix S S ℝ) (hP : IsErgodic P) (π : S → ℝ) (hπ : IsStationary P π)
    (ρ V0 : S → ℝ) :
    let W := (fundamentalMatrix P π - limitMatrix π) *ᵥ ρ + limitMatrix π *ᵥ V0
    ∀ i, W i + gain π ρ = ρ i + ∑ j, P i j * W j := by sorry

end JewellMRP.InfiniteStep
