-- Prove2me | Theorems.Thm_IndependentInfoPricing_Main_reverse_closure
-- name    : IndependentInfoPricing.Main.reverse_closure
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:32:28.804846+00:00
-- url     : https://prove2.me/theorems/cc06a363-e0eb-4f0f-97f8-592b88584090
-- title:
--   Proposition 2.2 — Reverse closure
-- statement:
--   Let $M$ be a finite menu of feasible binary experiments at nonnegative prices, containing both free options and the reverse $(1-x,p)$ of each entry $(x,p)$. For every real type vector $v$,
--
--   $$V_M(v)=U_M(v).$$
--
--   Moreover, some entry attains this common value by following its recommendation. Thus allowing the buyer all four action rules does not increase the best utility above the additive menu value. This is the implementability interface for reverse-closed menus.
--
--   Differences from the source:
--   - encoding: finite menu maxima and highest-price ties → real suprema of finite sets of utilities and maximizing prices; reason: both free entries ensure nonempty finite maximizing sets; maxima and seller-favorable ties are unchanged
--   - encoding: real expected revenues and independent coordinates indexed by [Q] → nonnegative extended integrals and suprema with coordinates indexed by Fin Q; reason: preserves arbitrary real product laws and infinite revenues without default-zero integration; Fin Q only relabels the finite states
-- source:
--   Hu Fu, Chenshuo Guo, STOC 2027 submission #1459 (October 2026), Proposition 2.2, printed pp.9–9 (PDF pp.11–11); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1459.pdf

import Definitions.Def_IndependentInfoPricing_Main_Menus

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

namespace IndependentInfoPricing.Main

/-- Proposition 2.2, p.9 (PDF 11). -/
theorem reverse_closure {Q : ℕ} (M : Menu (Fin Q)) (hM : ValidMenu M)
    (hr : ReverseClosed M) : ∀ v,
    menuValue true M v = menuValue false M v ∧
      ∃ e ∈ M, dot v e.1 - e.2 = menuValue true M v := by sorry

end IndependentInfoPricing.Main
