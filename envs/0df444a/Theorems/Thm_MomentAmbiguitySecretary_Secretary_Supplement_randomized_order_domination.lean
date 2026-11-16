-- Prove2me | Theorems.Thm_MomentAmbiguitySecretary_Secretary_Supplement_randomized_order_domination
-- name    : MomentAmbiguitySecretary.Secretary.Supplement.randomized_order_domination
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:54:08.352952+00:00
-- url     : https://prove2.me/theorems/eb2d1c3c-cf3e-4f0b-a5e1-3f6e7e633ed4
-- title:
--   Lemma 4.2 (used in the proof of Theorem 4.1) — Every finite-mean randomized order is dominated by ordering its mean
-- statement:
--   Let $\beta\in[0,1]$, let $\psi$ be a nonnegative demand law with finite first moment, and let $\lambda$ be any probability order law on $[0,\infty)$ with finite first moment. Put $\bar q=\int q\,d\lambda(q)$. The profit is integrable under $\lambda$ and
--   $$\operatorname{Profit}_{\psi,\beta}(\lambda)\le\operatorname{Profit}_{\psi,\beta}(\bar q).$$
--   The integrability conclusion is stated in the source proof. The inequality compares every finite-mean randomized order with its deterministic mean order, including unbounded laws and both endpoint values of $\beta$.
--
--   Differences from the source: none.
-- source:
--   Cristi, Russo & Zhang (2026), Moment Ambiguity and the Limits of Robust Stochastic Optimization, STOC 2027 submission #44, supplied checksum-pinned preprint. Lemma 4.2, PDF/printed p.10; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/44.pdf; SHA-256 8759453424e009e4e0380263fc1672d9622bea438cc43904e881469f456c9895

import Definitions.Def_MomentAmbiguitySecretary_Secretary_Supplement_Newsvendor

open MeasureTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology

namespace MomentAmbiguitySecretary.Secretary.Supplement

/-- Lemma 4.2, supplied preprint, PDF/printed p.10. -/
theorem randomized_order_domination (ψ : Distribution) (hψ : FiniteMean (ψ : Measure ℝ≥0))
    (β : ℝ) (hβ : β ∈ Icc 0 1) (lottery : OrderLaw) :
    Integrable (fun q : ℝ≥0 => profit (ψ : Measure ℝ≥0) β q)
      (lottery.val : Measure ℝ≥0) ∧
    randomizedProfit (ψ : Measure ℝ≥0) β lottery ≤
      profit (ψ : Measure ℝ≥0) β (meanOrder lottery) := by sorry

end MomentAmbiguitySecretary.Secretary.Supplement
