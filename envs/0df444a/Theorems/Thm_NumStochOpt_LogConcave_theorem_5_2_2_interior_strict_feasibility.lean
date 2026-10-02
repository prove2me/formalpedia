-- Prove2me | Theorems.Thm_NumStochOpt_LogConcave_theorem_5_2_2_interior_strict_feasibility
-- name    : NumStochOpt.LogConcave.theorem_5_2_2_interior_strict_feasibility
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T20:03:01.145297+00:00
-- url     : https://prove2.me/theorems/146ec960-40d6-4960-a44c-61d914ccb384
-- title:
--   Theorem 5.2.2 — at an interior point of the feasible set of (5.1) every constraint holds strictly
-- statement:
--   Consider problem (5.1): minimize $h(x)$ subject to $h_0(x) \ge p$ and $h_i(x) \ge p_i$, $i = 1, \dots, m$, where $h_0(x) = P(g_1(x,\xi) \ge 0, \dots, g_r(x,\xi) \ge 0)$. Assume the standing hypotheses of §5.2:
--
--   1. $0 < p < 1$, $p_1 > 0, \dots, p_m > 0$, and $h$ is convex on $\mathbb R^n$;
--   2. $h_1, \dots, h_m$ are continuous logarithmically concave functions on $\mathbb R^n$;
--   3. $g_1, \dots, g_r$ are (jointly) concave functions on $\mathbb R^{n+q}$;
--   4. the feasible set $D = \{x : h_0(x) \ge p,\ h_i(x) \ge p_i,\ i = 1, \dots, m\}$ is compact;
--   5. there is an $x$ with $h_i(x) > p_i$ for $i = 0, 1, \dots, m$ (where $p_0 = p$);
--   6. $\xi$ has a continuous probability distribution with a logarithmically concave density.
--
--   If $z$ is an interior (nonboundary) point of $D$, then
--
--   $$
--   h_i(z) > p_i, \qquad i = 0, 1, \dots, m .
--   $$
--
--   The theorem guarantees that the logarithmic penalty function (5.5), which is defined only where all constraints hold strictly, is defined on the whole interior of the feasible set.
--
--   **Formalization Note** The index $i = 0$ is the probabilistic constraint $h_0 \ge p$ and is stated separately; $h_1, \dots, h_m$ are indexed by `Fin m`. All six assumptions of §5.2 are hypotheses, including the convexity of the objective $h$, which the conclusion does not mention. Log-concavity of $h_0$ is not assumed: it follows from assumptions 3 and 6 by Theorem 5.1. "Nonboundary point of the set of feasible solutions" is membership in the topological interior of $D$. The density hypothesis is stated exactly as in Theorem 5.1.
-- source:
--   A. Prékopa, "Numerical Solution of Probabilistic Constrained Programming Problems", in Ermoliev & Wets (eds.), Numerical Techniques for Stochastic Optimization, Springer 1988, Ch. 5, §5.2, p. 126, Theorem 5.2.2 (assumptions of §5.2 on p. 125)

import Mathlib
import Definitions.Def_LogConcaveOn
import Definitions.Def_NumStochOpt_LogConcave_chanceProb

open MeasureTheory

namespace NumStochOpt.LogConcave

theorem theorem_5_2_2_interior_strict_feasibility
    {Ω : Type*} [MeasurableSpace Ω] {n q r m : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : Ω → EuclideanSpace ℝ (Fin q)) (hξ : Measurable ξ)
    (f : EuclideanSpace ℝ (Fin q) → ℝ) (hf_meas : Measurable f)
    (hf_lc : ConvexOptimization.LogConcaveOn Set.univ f)
    (hlaw : P.map ξ = volume.withDensity (fun y => ENNReal.ofReal (f y)))
    (g : Fin r → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin q) → ℝ)
    (hg : ∀ i, ConcaveOn ℝ Set.univ (g i))
    (h : EuclideanSpace ℝ (Fin n) → ℝ) (hh : ConvexOn ℝ Set.univ h)
    (hs : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (hs_cont : ∀ i, Continuous (hs i))
    (hs_lc : ∀ i, ConvexOptimization.LogConcaveOn Set.univ (hs i))
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (ps : Fin m → ℝ) (hps : ∀ i, 0 < ps i)
    (hD : IsCompact {x | p ≤ chanceProb P ξ g x ∧ ∀ i, ps i ≤ hs i x})
    (hslater : ∃ x, p < chanceProb P ξ g x ∧ ∀ i, ps i < hs i x)
    (z : EuclideanSpace ℝ (Fin n))
    (hz : z ∈ interior {x | p ≤ chanceProb P ξ g x ∧ ∀ i, ps i ≤ hs i x}) :
    p < chanceProb P ξ g z ∧ ∀ i, ps i < hs i z := by sorry

end NumStochOpt.LogConcave
