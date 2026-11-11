-- Prove2me | Theorems.Thm_IndependentInfoPricing_Main_orthant_relaxation
-- name    : IndependentInfoPricing.Main.orthant_relaxation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:34:39.99167+00:00
-- url     : https://prove2.me/theorems/d2b64147-0052-437c-b4ae-ab66d22e867e
-- title:
--   Lemma 4.17 — Orthant relaxation
-- statement:
--   Let the signed payoff coordinates have independent probability laws with no atom at zero. For each occurring sign set $S$, form its conditional product law and the operational classical optima $C_+(S),C_-(S)$ of the positive and negative blocks. Then
--
--   $$\operatorname{OPT}^{\rm rel}_S\le\min\{C_+(S),C_-(S)\},\qquad \operatorname{OPT}^{\rm rel}\le\mathbb E_S\min\{C_+(S),C_-(S)\}.$$
--
--   If a sign pattern has probability one, the global optimum obeys that pattern's same minimum bound, retaining (68). Empty blocks use their actual zero-dimensional classical selling problems. Conditional independence is represented by the branch product laws, rather than assumed as an additional inequality.
--
--   Differences from the source:
--   - generalization: Section 4 standing continuously differentiable marginal densities → independent probability marginals with no atom at zero; reason: the orthant argument uses conditional independence but no density or regularity; all source instances have no zero atom
--   - encoding: real expected revenues and independent coordinates indexed by [Q] → nonnegative extended integrals and suprema with coordinates indexed by Fin Q; reason: preserves arbitrary real product laws and infinite revenues without default-zero integration; Fin Q only relabels the finite states
-- source:
--   Hu Fu, Chenshuo Guo, STOC 2027 submission #1459 (October 2026), Lemma 4.17, printed pp.40–41 (PDF pp.42–43); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1459.pdf

import Definitions.Def_IndependentInfoPricing_Main_Analysis

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

namespace IndependentInfoPricing.Main

/-- Lemma 4.17, pp.40–42 (PDF 42–44), (67) and deterministic-sign (68). -/
theorem orthant_relaxation {Q : ℕ} (F : Marginals (Fin Q))
    (hF : ProbabilityMarginals F) (hz : ∀ i, F i {0} = 0) :
    (∀ S : Finset (Fin Q), signWeight F S ≠ 0 →
      optRelOn (orthant S) (orthantLaw F S) ≤ min (positiveClassical F S) (negativeClassical F S)) ∧
    optRel (productLaw F) ≤ signExpectation F (fun S => min (positiveClassical F S) (negativeClassical F S)) ∧
    (∀ S : Finset (Fin Q), signWeight F S = 1 →
      optRel (productLaw F) ≤ min (positiveClassical F S) (negativeClassical F S)) := by sorry

end IndependentInfoPricing.Main
