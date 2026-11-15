-- Prove2me | Theorems.Thm_GibbsTransition_SizeCopies_Supplement_adaptive_indistinguishability
-- name    : GibbsTransition.SizeCopies.Supplement.adaptive_indistinguishability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:38:49.709507+00:00
-- url     : https://prove2.me/theorems/b38dbfd4-7476-4aa6-87ff-25c7f673e3e5
-- title:
--   Lemma 4.3 — Adaptive indistinguishability
-- statement:
--   Suppose two physical state suppliers return the same density matrix at every allowed dyadic field and every positive side $L\le R$. For any instance-independent adaptive experiment, let $\nu_i$ be the output subprobability measure on rational estimates obtained by terminating without requesting a side exceeding $R$, and let $p_i$ be the probability of ever making such a request. Then
--   $$\nu_0=\nu_1,\qquad p_0=p_1.$$
--   The first equality is equality of measures on every measurable output set, not just a success event. The experiment may retain arbitrary quantum memory, have arbitrary measurable outcomes and run without a fixed horizon; the lemma does not require almost-sure termination.
--
--   This identifies the complete observable experiment before the first oversized query.
--
--   Differences from the source:
--   - encoding: output subprobability measure and first oversized query → increasing finite-horizon measures and query-event probabilities on the published memory/instrument semantics; reason: this includes all measurable output sets and arbitrary stopping horizons
--   - generalization: two source-model instances returning identical states below the size cap → any finite local dimension and any two physical fresh-state suppliers identical on all allowed capped queries; reason: the source argument uses only equality of the supplied states and instance independence of the instruments; the source-model suppliers specialize to this statement
-- source:
--   Yuhao Cai, Zhenzhang Li, STOC 2027 submission #1168 (October 2026), Lemma 4.3, printed p. 8 (PDF p. 10); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1168.pdf

import Mathlib
import Definitions.Def_GibbsTransition_SizeCopies_Supplement_Access
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
set_option autoImplicit false

namespace GibbsTransition.SizeCopies.Supplement

theorem adaptive_indistinguishability
    {q : ℕ} (hq : 0 < q) (S0 S1 : Supplier q)
    (h0 : ∀ query, IsMemoryState (S0 query))
    (h1 : ∀ query, IsMemoryState (S1 query)) (R : ℕ)
    (heq : ∀ query : CubeQuery, query.side ≤ R → S0 query = S1 query)
    {O ι : Type} [MeasurableSpace O] (A : AccessExperiment q O ι)
    (hA : IsAccessExperiment A) :
    beforeOversizedOutput A S0 R = beforeOversizedOutput A S1 R ∧
    oversizedProbability A S0 R = oversizedProbability A S1 R := by sorry

end GibbsTransition.SizeCopies.Supplement
