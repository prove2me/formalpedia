-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_contact_stepA_readable
-- name    : FunctionalInequalities.Analysis.contact_stepA_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:11.734626+00:00
-- url     : https://prove2.me/theorems/8b79d3f8-eb05-43a8-ba70-26607440bbcb
-- title:
--   Contact Image Volume Bound
-- statement:
--   This is an auxiliary geometric estimate for subgradient images.
--
--   Let $E$ be a nontrivial finite-dimensional real inner-product space with its Borel measurable structure, let $v:E\to\mathbb R$, let $S\subseteq E$, and let $A,t\in\mathbb R$. Assume:
--
--   1. $0<t$.
--   2. The unit ball satisfies $B(0,1)\subseteq S$.
--   3. For every $x\in S$, $-2t\le v(x)$.
--   4. For every $x\in S$, $v(x)\le 0$.
--   5. With `subgradientImage` denoting the subgradient image, the volume comparison
--      $$A\,\operatorname{vol}(B(0,1/2))\le \operatorname{vol}(\partial v(B(0,1/2)))$$
--      holds after taking the real `toReal` values of the corresponding `ENNReal` measures.
--
--   Then, writing $n=\operatorname{finrank}_{\mathbb R}E$, one has
--   $$A\le (8t)^n.$$
--
--   This is a technical scaling estimate used in the localized Caffarelli contact-set argument.
--
--   **Formalization Note** The measure values are in $[0,\infty]$ (`ENNReal`), and the displayed comparison and conclusion use their real `toReal` coercions. The exponent is the real dimension of $E$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private lemma contact_stepA
--       [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
--       {v : E → ℝ} {S : Set E} {A t : ℝ} (ht : 0 < t)
--       (hball : ball (0 : E) 1 ⊆ S)
--       (hlo : ∀ x ∈ S, -2 * t ≤ v x)
--       (hhi : ∀ x ∈ S, v x ≤ 0)
--       (hA : A * ((volume : Measure E) (ball (0 : E) (1 / 2))).toReal ≤
--         (volume (subgradientImage v (ball (0 : E) (1 / 2)))).toReal) :
--       A ≤ (8 * t) ^ Module.finrank ℝ E
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Caffarelli`](https://prove2.me/theorems/9215c92e-8aaf-4fc3-85d3-101608b4064d).
--
--   Definition modules: [`Analysis/Convex/Subgradient`](https://prove2.me/theorems/67a77afb-a546-4173-875a-237133f9cad7).
--
--   Previous: [`exists_compact_sections_subset_and_shrink`](https://prove2.me/theorems/e7f0ab2e-a85f-430a-8fd7-c28dea0e4a20) · Next: [`contactSet_eq_singleton_of_exposed_of_local_bounds`](https://prove2.me/theorems/b68b47d0-6adf-4db3-9250-a72ca18aaa5f).
--
--   [Source excerpt, lines 501–509](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Caffarelli.lean#L501-L509) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Caffarelli.lean#L501-L581 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Caffarelli`, declaration `_private.FunctionalInequalities.Analysis.Convex.Caffarelli.0.FunctionalInequalities.Analysis.contact_stepA`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Caffarelli

open MeasureTheory Set Metric
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

lemma FunctionalInequalities.Analysis.contact_stepA_readable
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    {v : E → ℝ} {S : Set E} {A t : ℝ} (ht : 0 < t)
    (hball : ball (0 : E) 1 ⊆ S)
    (hlo : ∀ x ∈ S, -2 * t ≤ v x)
    (hhi : ∀ x ∈ S, v x ≤ 0)
    (hA : A * ((volume : Measure E) (ball (0 : E) (1 / 2))).toReal ≤
      (volume (subgradientImage v (ball (0 : E) (1 / 2)))).toReal) :
    A ≤ (8 * t) ^ Module.finrank ℝ E := by sorry
