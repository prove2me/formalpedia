-- Prove2me | Theorems.Thm_KTaxi_Competitive_Supplement_lemma_C_2
-- name    : KTaxi.Competitive.Supplement.lemma_C_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:32:24.402193+00:00
-- url     : https://prove2.me/theorems/0ce130c4-70db-4deb-9b3f-c61632fcad34
-- title:
--   Lemma C.2 — one probability for both oriented comparisons
-- statement:
--   Under the same lazy memoryless and finite oblivious competitiveness assumptions as Lemma C.1, use the same algorithm-dependent supremum $F_A$. For every pairwise distinct $x,y,z\in\mathbb R$, there is a single $p\in[0,1]$ such that
--   $$F_A(x,y)\ge p|x-y|+(1-p)(|z-y|+F_A(x,z)),$$
--   $$F_A(z,y)\ge (1-p)|z-y|+p(|x-y|+F_A(z,x)).$$
--   These simultaneous constraints compare the same online serving-location law with two offline configurations. The continuations defining each supremum are fixed in advance, so the result retains the oblivious setting. Finiteness follows from C.1 under the inherited assumptions; no real-valued conversion is performed.
--
--   Differences from the source:
--   - encoding: lazy memoryless randomized algorithms → a PMF on serving locations indexed by an unordered multiset and the current request; reason: the source specifies this history-conditioned law; its support has at most two locations, and irrelevant internal state does not change expected costs
--   - encoding: an additive constant independent of the finite oblivious request sequence → fixed common initial configuration and finite nonnegative ρ and β before the request list; reason: the Appendix C proof prepares the defining configurations for free from every fixed common start; nonnegative constants suffice for every finite competitive bound
--   - encoding: expected nonnegative hard costs → extended nonnegative real expectations; reason: retains infinite costs and charges only paid movement, with no nonintegrable Bochner default
--   - encoding: p ∈ [0,1] → p is a nonnegative real with p ≤ 1; reason: the truncated nonnegative subtraction 1−p equals the ordinary complement on this interval
-- source:
--   Christian Coester, Yichen Huang, Tze-Yang Poon, STOC 2027 submission #96 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/96.pdf, Lemma C.2, PDF p. 24 (printed p. 23)

import Mathlib
import Definitions.Def_KTaxi_Competitive_Supplement_Memoryless

open scoped ENNReal NNReal

namespace KTaxi.Competitive.Supplement

/-- Lemma C.2, PDF p. 24. The same p satisfies both comparisons for the actual
oriented supremum. By C.1 (under precisely these inherited hypotheses) it is finite;
ENNReal retains its value without any premature toReal conversion. -/
theorem lemma_C_2 (A : MemorylessPolicy) (x₀ : Fin 2 → ℝ) (ρ β : ℝ≥0)
    (hρ : 1 ≤ ρ) (hcomp : ObliviousCompetitive A x₀ ρ β)
    (x y z : ℝ) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ p : ℝ≥0, p ≤ 1 ∧
      (p : ℝ≥0∞) * edist x y + ((1 - p : ℝ≥0) : ℝ≥0∞) *
        (edist z y + discrepancy A x z) ≤ discrepancy A x y ∧
      ((1 - p : ℝ≥0) : ℝ≥0∞) * edist z y + (p : ℝ≥0∞) *
        (edist x y + discrepancy A z x) ≤ discrepancy A z y := by sorry

end KTaxi.Competitive.Supplement
