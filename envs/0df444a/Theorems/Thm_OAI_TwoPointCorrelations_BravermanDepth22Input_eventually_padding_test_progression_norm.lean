-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_BravermanDepth22Input_eventually_padding_test_progression_norm
-- name    : OAI.TwoPointCorrelations.BravermanDepth22Input.eventually_padding_test_progression_norm
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:31.333931+00:00
-- url     : https://prove2.me/theorems/1cd50ef5-11f7-4f9f-b79b-a29995154a34
-- title:
--   Under Braverman's theorem, the mean square of the padding test vector along a progression
-- statement:
--   Assume `BravermanDepth22Input` (Braverman's theorem for depth-22 AC⁰ circuits). Then there is a natural $A\ge1000$ such that for all sufficiently large $L$: for every finite set $Q$ of primes, each at most $e^L$, every finite type $V$ with a site map $V\to\mathbb Z$, every $f:\mathbb Z\to\mathbb C$ with $|f|\le1$, and all naturals $a,l,N$ with $l>0$ and $N\ge\exp(L^A/2)$,
--
--   $$\frac1N\sum_{x<N}\big\|\texttt{paddingTestVector}\,Q\,L\,(i\mapsto a+lx+\mathrm{site}(i))\,f\big\|^2\le l\cdot 2\,|V|\cdot\texttt{paddingTiltNormalizer}(Q),$$
--
--   where `paddingTestVector` and `paddingTiltNormalizer` are defined in the bundle.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.BravermanDepth22Input.eventually_padding_test_progression_norm`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open Filter
open scoped Classical

theorem BravermanDepth22Input.eventually_padding_test_progression_norm
    (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (Q : Finset ℕ), (∀ p ∈ Q, p.Prime) →
      (∀ p ∈ Q, (p : ℝ) ≤ Real.exp L) →
      ∀ {V : Type*} [Fintype V] (site : V → ℤ) (f : ℤ → ℂ), (∀ n, ‖f n‖ ≤ 1) →
      ∀ a l N : ℕ, 0 < l → Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      uniformAverage (fun x : Fin N => ‖paddingTestVector Q L
        (fun i => ((a + l * x.val : ℕ) : ℤ) + site i) f‖ ^ 2) ≤
        (l : ℝ) * (2 * Fintype.card V * paddingTiltNormalizer Q) := by
  sorry

end OAI.TwoPointCorrelations
