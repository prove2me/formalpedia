-- Prove2me | Theorems.Thm_KTaxi_Competitive_Supplement_theorem_1_3
-- name    : KTaxi.Competitive.Supplement.theorem_1_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:33:39.923051+00:00
-- url     : https://prove2.me/theorems/e6631cb1-fabc-46cf-8675-e725097aa546
-- title:
--   Theorem 1.3 — infinite oblivious ratio for every lazy memoryless policy
-- statement:
--   Let $A$ be any lazy memoryless randomized online two-taxi algorithm on the full real line and fix any common initial configuration $x_0$. For every finite $\rho\ge1$ and $\beta\ge0$, there exists a finite request list $\sigma$, fixed before the random outcomes, such that
--   $$\mathbb E[A(\sigma)]>\rho\operatorname{OPT}_{x_0}(\sigma)+\beta.$$
--   Thus every such algorithm has infinite competitive ratio even against oblivious adversaries. Its serving-location law may depend on the destination, orientation and absolute position; no reflection invariance or other regularity is assumed. Lemmas C.1–C.3 support this companion theorem, which is not used in the proof of the mission goal.
--
--   Differences from the source:
--   - encoding: lazy memoryless randomized algorithms → a PMF on serving locations indexed by an unordered multiset and the current request; reason: the source specifies this history-conditioned law; its support has at most two locations, and irrelevant internal state does not change expected costs
--   - encoding: an additive constant independent of the finite oblivious request sequence → fixed common initial configuration and finite nonnegative ρ and β before the request list; reason: the Appendix C proof prepares the defining configurations for free from every fixed common start; nonnegative constants suffice for every finite competitive bound
--   - encoding: expected nonnegative hard costs → extended nonnegative real expectations; reason: retains infinite costs and charges only paid movement, with no nonintegrable Bochner default
-- source:
--   Christian Coester, Yichen Huang, Tze-Yang Poon, STOC 2027 submission #96 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/96.pdf, Theorem 1.3, PDF p. 23 (printed p. 22)

import Mathlib
import Definitions.Def_KTaxi_Competitive_Supplement_Memoryless

open scoped ENNReal NNReal

namespace KTaxi.Competitive.Supplement

/-- Theorem 1.3, PDF pp. 3, 15, 23. Full real line, every fixed common start,
oblivious finite request lists, arbitrary finite additive constant. -/
theorem theorem_1_3 (A : MemorylessPolicy) (x₀ : Fin 2 → ℝ)
    (ρ β : ℝ≥0) (hρ : 1 ≤ ρ) :
    ∃ qs : List (ℝ × ℝ),
      (ρ : ℝ≥0∞) * optCost x₀ qs + (β : ℝ≥0∞) <
        memorylessCost A (locations x₀) qs := by sorry

end KTaxi.Competitive.Supplement
