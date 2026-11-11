-- Prove2me | Theorems.Thm_IndependentInfoPricing_Main_symmetrization
-- name    : IndependentInfoPricing.Main.symmetrization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:32:11.159706+00:00
-- url     : https://prove2.me/theorems/860a9031-ac6b-4df1-a82a-f0f5126e3d9b
-- title:
--   Lemma 2.3 — Symmetrization
-- statement:
--   Let $M$ be any finite feasible menu containing both free options. Its ordered-pair symmetrization is feasible, reverse closed, contains both free options, and admits a measurable truthful implementation with seller-favorable ties. For every type $v$,
--
--   $$U_{\operatorname{Sym}(M)}(v)=\frac{\sum_i v_i+U_M(v)+U_M(-v)}{2},\qquad p^{\rm rel}_{\operatorname{Sym}(M)}(v)\ge\tfrac12p^{\rm rel}_M(v).$$
--
--   For every probability law of the types,
--
--   $$\operatorname{Rev}(\operatorname{Sym}(M))\ge\tfrac12\operatorname{Rev}^{\rm rel}(M).$$
--
--   This is the conversion from additive menu revenue to actual information revenue; no symmetry assumption on the type law is imposed.
--
--   Differences from the source:
--   - encoding: finite menu maxima and highest-price ties → real suprema of finite sets of utilities and maximizing prices; reason: both free entries ensure nonempty finite maximizing sets; maxima and seller-favorable ties are unchanged
--   - encoding: real expected revenues and independent coordinates indexed by [Q] → nonnegative extended integrals and suprema with coordinates indexed by Fin Q; reason: preserves arbitrary real product laws and infinite revenues without default-zero integration; Fin Q only relabels the finite states
-- source:
--   Hu Fu, Chenshuo Guo, STOC 2027 submission #1459 (October 2026), Lemma 2.3, printed pp.9–9 (PDF pp.11–11); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1459.pdf

import Definitions.Def_IndependentInfoPricing_Main_Menus

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

namespace IndependentInfoPricing.Main

/-- Lemma 2.3, p.9 (PDF 11), all of (12)–(13). -/
theorem symmetrization {Q : ℕ} (M : Menu (Fin Q)) (hM : ValidMenu M)
    (F : Measure (Values (Fin Q))) [IsProbabilityMeasure F] :
    ValidMenu (symmetrize M) ∧ ReverseClosed (symmetrize M) ∧ ImplementsMenu (symmetrize M) ∧
    (∀ v, menuValue false (symmetrize M) v =
      ((∑ i, v i) + menuValue false M v + menuValue false M (-v)) / 2 ∧
      menuPayment false M v / 2 ≤ menuPayment false (symmetrize M) v) ∧
    (1 / 2 : ℝ≥0∞) * menuRevenue false F M ≤ menuRevenue true F (symmetrize M) := by sorry

end IndependentInfoPricing.Main
