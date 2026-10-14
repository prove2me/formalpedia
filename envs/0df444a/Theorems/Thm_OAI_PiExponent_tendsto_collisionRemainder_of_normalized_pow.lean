-- Prove2me | Theorems.Thm_OAI_PiExponent_tendsto_collisionRemainder_of_normalized_pow
-- name    : OAI.PiExponent.tendsto_collisionRemainder_of_normalized_pow
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-11T21:03:18.818204+00:00
-- url     : https://prove2.me/theorems/3d02d61e-2783-4a0c-82ca-a411ca66c0fc
-- title:
--   Vanishing collision remainder for polynomially normalized counts
-- statement:
--   Let $M:\mathbb R\to\mathbb N$, $d\in\mathbb N$, and $L>0$. Suppose $M(H)/H^d\to L$ as $H\to+\infty$. For the original collision ratio $r=\exp(-\log 2/2)$, the collision remainder satisfies
--
--   $$\frac{\log M(H)+\log 2/4-\log(1-r)}{H}\longrightarrow0.$$
--
--   This generic limit is the collision-remainder child used by the original analytic aggregate proof.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean#L56-L64

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData

open scoped BigOperators Topology
open Filter
open OAI.PiExponent

theorem OAI.PiExponent.tendsto_collisionRemainder_of_normalized_pow {M : ℝ → ℕ} {d : ℕ} {L : ℝ}
    (hM : Tendsto (fun H : ℝ => (M H : ℝ) / H ^ d) atTop (𝓝 L)) (hL : 0 < L) :
    Tendsto (fun H => Collision.collisionRemainder (M H) H) atTop (𝓝 0) := by
  sorry
