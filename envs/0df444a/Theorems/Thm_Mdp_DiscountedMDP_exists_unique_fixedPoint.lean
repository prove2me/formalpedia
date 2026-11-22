-- Prove2me | Theorems.Thm_Mdp_DiscountedMDP_exists_unique_fixedPoint
-- name    : Mdp.DiscountedMDP.exists_unique_fixedPoint
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:02:41.943806+00:00
-- url     : https://prove2.me/theorems/b2ffc9bf-17c9-48d9-a213-ef530ab42f33
-- title:
--   Discounted MDP: exists unique fixed Point
-- statement:
--   **The payoff.** `M.bellman` has exactly one fixed point — corresponds to
--       `\<L>\<^sub>b_conv`/`\<nu>\<^sub>b_opt` in `MDP_reward.thy`, but where Isabelle has to build
--       its own Banach fixed point argument (`is_contraction`, `banach'`) from scratch, this falls out
--       of `ContractingWith.exists_fixedPoint` (existence, from completeness of `S → ℝ` as a
--       `Fintype`-indexed Pi type) plus a five-line direct argument for uniqueness (two fixed points
--       would each be a contraction-factor away from the other, forcing distance `0`). `(0 : S → ℝ)`
--       as the iteration basepoint is arbitrary — any starting point works. Every Mathlib name here
--       (`LipschitzWith.of_dist_le_mul`, `ContractingWith`, `exists_fixedPoint`'s 4-way return,
--       `edist_ne_top`) confirmed by `lake build` as written; the one bug was `∃!`'s uniqueness clause
--       unfolding as `w = v`, not `v = w` — flipped which side `by_contra`'s hypothesis needed
--       `.symm`ed.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Mdp/Basic.lean#L207-L215
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Mdp/Basic.lean#L207-L215

import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Group.Basic
import Definitions.Def_Mdp_Basic
set_option autoImplicit true
open Mdp
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
open Mdp.DiscountedMDP
variable (M : DiscountedMDP S A)

theorem Mdp.DiscountedMDP.exists_unique_fixedPoint : ∃! v : S → ℝ, M.bellman v = v := by sorry
