-- Prove2me | Theorems.Thm_OAI_PiExponent_FiniteMinorAnalysis_690acb6f_scalar_bound_and_support
-- name    : OAI.PiExponent.FiniteMinorAnalysis_690acb6f.scalar_bound_and_support
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T09:27:50.683111+00:00
-- url     : https://prove2.me/theorems/2284aaa1-ec45-48ea-aa4d-7e6bfdfe5e2f
-- title:
--   Finite approximation controls each literal translation scalar
-- statement:
--   Each literal translation scalar satisfies the approximation-and-tail exponential bound, and a nonzero scalar has transverse weight at least the original row weight. Prove the estimate from the rational approximation bound and truncation-tail coefficient support; the nonzero implication follows from the finite binomial factors.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PiExponent.lean

import Definitions.Def_PiExponent_FiniteTranslationData_690acb6f
open OAI.PiExponent
open OAI.PiExponent.FiniteMinorAnalysis_690acb6f
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.FiniteMinorAnalysis_690acb6f.scalar_bound_and_support
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
