-- Prove2me | Theorems.Thm_KarlinDynamicProgramming_Uniqueness_bellman_two_step_expansion
-- name    : KarlinDynamicProgramming.Uniqueness.bellman_two_step_expansion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:55:33.561782+00:00
-- url     : https://prove2.me/theorems/8fc7f6b4-5901-4293-bf01-ac23659bd543
-- title:
--   Uniqueness, first unnumbered display — two-step Bellman expansion
-- statement:
--   Under the standing Hausdorff-state, nonempty compact Hausdorff-decision, stationary reward and product-weight assumptions and finite uniform convergence of returns, let M be any real attained Bellman solution. At every state its Bellman maximum equals the outer maximum of the inner Bellman maxima, and also the two nested attained maxima of L(ω,a) + P(a)L(Taω,b) + P(a)P(b)M(Tb(Taω)). Both inner and outer maxima are attained.
--
--   Differences from the source:
--   - encoding: first and second decisions δ₁, δ₂ with ω₃ = Tδ₂(Tδ₁ω) → a, b with m.T b (m.T a ω); reason: the two decisions and reached state are unchanged
--   - encoding: attained maxima written as max → IsGreatest of the actual range, with existential inner maximum functions in the two-step display; reason: membership asserts attainment and the upper-bound clause asserts dominance over every allowed decision or strategy
-- source:
--   Karlin, The Structure of Dynamic Programing Models, Naval Research Logistics Quarterly 2(4) (1955), 285–294, doi:10.1002/nav.3800020408; Uniqueness, first unnumbered display, PDF 7 / printed 291

import Definitions.Def_KarlinDynamicProgramming_Uniqueness_CandidateSolutions

namespace KarlinDynamicProgramming.Uniqueness

/-- Uniqueness, first unnumbered display, printed p. 291 (PDF 7).
All three maxima, including the inner second-decision maxima, are attained. -/
theorem bellman_two_step_expansion
    {Ω D : Type*} [TopologicalSpace Ω] [T2Space Ω]
    [TopologicalSpace D] [T2Space D] [CompactSpace D] [Nonempty D]
    (m : Model Ω D) (hreturns : UniformFiniteReturns m)
    (M : Ω → ℝ) (hM : BellmanSolution m M) (ω : Ω) :
    IsGreatest (Set.range (bellmanAction m M ω)) (M ω) ∧
    (∃ B : D → ℝ,
      (∀ a, IsGreatest (Set.range (bellmanAction m M (m.T a ω))) (B a)) ∧
      IsGreatest (Set.range (fun a => m.L ω a + m.P a * B a)) (M ω)) ∧
    (∃ V : D → ℝ,
      (∀ a, IsGreatest (Set.range (twoStepValue m M ω a)) (V a)) ∧
      IsGreatest (Set.range V) (M ω)) := by sorry

end KarlinDynamicProgramming.Uniqueness
