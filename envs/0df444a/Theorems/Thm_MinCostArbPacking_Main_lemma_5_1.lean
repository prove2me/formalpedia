-- Prove2me | Theorems.Thm_MinCostArbPacking_Main_lemma_5_1
-- name    : MinCostArbPacking.Main.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:45:34.978183+00:00
-- url     : https://prove2.me/theorems/8930d30b-4369-4b42-9d69-4333efccd523
-- title:
--   Lemma 5.1 — local optimality conditions for minimum-cost independent sets
-- statement:
--   **Lemma 5.1 (Local optimality conditions).** Let $M$ be a matroid with costs $a$ on its finite ground set and let $I$ be independent. Then $I$ minimizes $a$ over all independent sets iff
--
--   $$\begin{aligned} a(f)&\le 0 && \text{for } f\in I, &(5.2)\\ a(e)&\ge 0 && \text{for } e\notin I \text{ with } I+e \text{ independent}, &(5.3)\\ a(e)&\ge a(f) && \text{for } e\notin I \text{ with } I+e \text{ dependent, and } f\in I \text{ with } I-f+e \text{ independent}. &(5.4)\end{aligned}$$
--
--   It is the certificate used to maintain the price invariant (5.1).
--
--   Differences from the source:
--   - encoding: a matroid on its ground set → a Mathlib matroid with ground set the whole finite type; reason: the same objects
-- source:
--   Zhaienhe Zhou, STOC 2027 submission #1416 (October 2026), §5.1, p.23, Lemma 5.1

import Mathlib
import Definitions.Def_MinCostArbPacking_Main_Exchange
set_option autoImplicit false

namespace MinCostArbPacking.Main

/-- Lemma 5.1 (Local optimality conditions), p.23: for a matroid `M` with costs `a` and an
independent set `I`, `I` minimizes `a` over all independent sets iff (5.2) `a(f) ≤ 0` for `f ∈ I`,
(5.3) `a(e) ≥ 0` for `e ∉ I` with `I + e` independent, and (5.4) `a(e) ≥ a(f)` for `e ∉ I` with
`I + e` dependent and `f ∈ I` with `I - f + e` independent. -/
theorem lemma_5_1 {α : Type} [Fintype α] [DecidableEq α] (M : Matroid α) (hM : M.E = Set.univ) (a : α → ℝ) (I : Finset α)
    (hI : matInd M I) :
    (∀ X, matInd M X → cost a I ≤ cost a X) ↔
      ((∀ f ∈ I, a f ≤ 0) ∧ (∀ e, e ∉ I → matInd M (insert e I) → 0 ≤ a e) ∧
        ∀ e, e ∉ I → ¬ matInd M (insert e I) → ∀ f ∈ I, matInd M (insert e (I.erase f)) →
          a f ≤ a e) := by sorry

end MinCostArbPacking.Main
