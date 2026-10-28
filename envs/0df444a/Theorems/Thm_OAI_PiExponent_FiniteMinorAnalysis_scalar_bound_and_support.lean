-- Prove2me | Theorems.Thm_OAI_PiExponent_FiniteMinorAnalysis_scalar_bound_and_support
-- name    : OAI.PiExponent.FiniteMinorAnalysis.scalar_bound_and_support
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T09:19:27.671145+00:00
-- url     : https://prove2.me/theorems/4d27a428-2ca0-4dec-9f6e-4cee0ce85129
-- title:
--   Finite approximation controls each literal translation scalar
-- statement:
--   Each explicitly defined translation scalar satisfies the approximation-and-tail exponential bound; a nonzero scalar has transverse weight at least the original row weight. The exact constants are the translation part of analyticError, and no infinite approximation family is required.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PiExponent.lean

import Definitions.Def_PiExponent_FiniteTranslationData
open OAI.PiExponent
open OAI.PiExponent.FiniteMinorAnalysis
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.FiniteMinorAnalysis.scalar_bound_and_support
    {m : ℕ} (K : ℕ) (v theta nu F wmin H : ℝ)
    (p : Fin m → ℤ) (q : Fin m → ℕ)
    (hK : 0 < K) (hv : 0 < v) (htheta : 0 < theta)
    (hnu : 0 ≤ nu) (hF : 0 < F) (hmin : 0 < wmin) (hH : 0 < H)
    (hq : ∀ i, 2 ≤ q i)
    (hwmin : ∀ i, wmin ≤ MatrixArithmetic.logWeights q i)
    (happrox : ∀ i, |Real.pi - (p i : ℝ) / (q i : ℝ)| ≤ (q i : ℝ) ^ (-nu)) :
    ∀ (r : Rows K v theta q H) (t : RowChoice r),
      ‖scalar F p q r t‖ ≤ Real.exp
        (-nu * (weight q t.1.1 - weight q (beta r)) +
          H * translationError K nu F v wmin) ∧
      (scalar F p q r t ≠ 0 → weight q (beta r) ≤ weight q t.1.1) := by sorry
