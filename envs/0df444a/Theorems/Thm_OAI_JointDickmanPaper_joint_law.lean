-- Prove2me | Theorems.Thm_OAI_JointDickmanPaper_joint_law
-- name    : OAI.JointDickmanPaper.joint_law
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:49.27689+00:00
-- url     : https://prove2.me/theorems/bd109978-c0be-4089-87dc-884370205a25
-- statement:
--   The theorem states that, for real numbers a and b with 0<a<1 and 0<b<1, the density of the set of integers n≥2 such that both the largest prime factor of n is at most n^a and the largest prime factor of n+1 is at most n^b converges, as X→∞, to ρ(1/a)·ρ(1/b). Here the density is the count of such n in the range 2≤n≤X divided by the real endpoint X, with the count taken up to ⌊X⌋. The largest prime factor is the last entry of the ascending prime factor list, with the defaults that it equals 0 at 0 and 1 at 1. Both thresholds are powers of n itself, not of n+1. The function ρ is defined by a delay-equation construction: ρ(u)=stepApprox(−1, ⌈u⌉)(u), where stepApprox starts from the constant 1 and iterates u ↦ 1 − ∫ from 1 to max(1,u) of f(t−1)/max(1,t) dt. The theorem is stated with its proof admitted (sorry).
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/JointDickman.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/JointDickman.lean; bytes 1191..1625
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_JointDickman

namespace OAI

namespace JointDickmanPaper

open Filter JointDickman

open scoped Topology

/-- Theorem 1: ordinary natural density, with both thresholds based at `n`. -/
theorem joint_law (a b : ℝ) (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1) :
    Tendsto (realDensity (fun n =>
      (n.maxPrimeFac : ℝ) ≤ (n : ℝ) ^ a ∧ ((n + 1).maxPrimeFac : ℝ) ≤ (n : ℝ) ^ b))
      atTop (𝓝 (Erdos970.NumberTheoryLean.Dickman.rho (1 / a) *
        Erdos970.NumberTheoryLean.Dickman.rho (1 / b))) := by
  sorry

end JointDickmanPaper
end OAI
