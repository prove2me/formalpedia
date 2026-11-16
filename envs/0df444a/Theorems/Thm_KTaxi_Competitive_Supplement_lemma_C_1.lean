-- Prove2me | Theorems.Thm_KTaxi_Competitive_Supplement_lemma_C_1
-- name    : KTaxi.Competitive.Supplement.lemma_C_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:31:54.917084+00:00
-- url     : https://prove2.me/theorems/d0c21819-4659-4623-b3ef-6289fe80ba20
-- title:
--   Lemma C.1 — oriented discrepancy distance bounds
-- statement:
--   Fix a lazy memoryless randomized two-taxi algorithm $A$ on $\mathbb R$, a common initial configuration $x_0$, and finite constants $\rho\ge1$, $\beta\ge0$. Assume its expected hard cost on every fixed finite request list is at most $\rho\operatorname{OPT}_{x_0}+\beta$. Let $F_A$ be its actual oriented discrepancy supremum over zero-cost offline request lists, with online start $\{x,x\}$ and offline start $\{x,y\}$. Then for every $x,y\in\mathbb R$,
--   $$|x-y|\le F_A(x,y)\le\rho|x-y|.$$
--   In particular the supremum is finite, its diagonal value is zero, and the additive constant disappears. This is the distance control used in the contradiction proving Theorem 1.3.
--
--   Differences from the source:
--   - encoding: lazy memoryless randomized algorithms → a PMF on serving locations indexed by an unordered multiset and the current request; reason: the source specifies this history-conditioned law; its support has at most two locations, and irrelevant internal state does not change expected costs
--   - encoding: an additive constant independent of the finite oblivious request sequence → fixed common initial configuration and finite nonnegative ρ and β before the request list; reason: the Appendix C proof prepares the defining configurations for free from every fixed common start; nonnegative constants suffice for every finite competitive bound
--   - encoding: expected nonnegative hard costs → extended nonnegative real expectations; reason: retains infinite costs and charges only paid movement, with no nonintegrable Bochner default
-- source:
--   Christian Coester, Yichen Huang, Tze-Yang Poon, STOC 2027 submission #96 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/96.pdf, Lemma C.1, PDF p. 23 (printed p. 22)

import Mathlib
import Definitions.Def_KTaxi_Competitive_Supplement_Memoryless

open scoped ENNReal NNReal

namespace KTaxi.Competitive.Supplement

/-- Lemma C.1, PDF p. 23. Appendix C's inherited contradiction setup is explicit.
The upper bound removes β and implies finiteness, including F(x,x)=0. -/
theorem lemma_C_1 (A : MemorylessPolicy) (x₀ : Fin 2 → ℝ) (ρ β : ℝ≥0)
    (hρ : 1 ≤ ρ) (hcomp : ObliviousCompetitive A x₀ ρ β) :
    ∀ x y : ℝ, edist x y ≤ discrepancy A x y ∧
      discrepancy A x y ≤ (ρ : ℝ≥0∞) * edist x y := by sorry

end KTaxi.Competitive.Supplement
