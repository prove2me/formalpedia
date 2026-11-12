-- Prove2me | Theorems.Thm_MinCostArbPacking_Main_lemma_4_3
-- name    : MinCostArbPacking.Main.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:45:07.789328+00:00
-- url     : https://prove2.me/theorems/e2a27e1d-fac6-4610-b860-9917e57f3c1b
-- title:
--   Lemma 4.3 — only the last element of a shortest augmenting path is free
-- statement:
--   **Lemma 4.3 (Only the last element is free).** Let $I$ be extreme (for a matroid $M$ and its class counts), and let $P=(e_0,f_0,\dots,f_{q-1},e_q)$ be a shortest augmenting path from class $u$. Then
--
--   $$e_0,\dots,e_{q-1}\notin X_1(I).$$
--
--   It makes shortest augmenting paths stop at their first free element, which is what localizes them to tight blocks.
--
--   **Formalization Note** The conclusion is stated for every element of $P$ except the last; elements of $I$ are never in $X_1(I)$.
--
--   Differences from the source: none.
-- source:
--   Zhaienhe Zhou, STOC 2027 submission #1416 (October 2026), §4.1, p.10, Lemma 4.3

import Mathlib
import Definitions.Def_MinCostArbPacking_Main_Exchange
set_option autoImplicit false

namespace MinCostArbPacking.Main

/-- Lemma 4.3 (Only the last element is free), p.10: if `I` is extreme and
`P = (e₀, f₀, …, f_{q-1}, e_q)` is a shortest augmenting path from class `u`, then
`e₀, …, e_{q-1} ∉ X₁(I)`. -/
theorem lemma_4_3 {α V : Type} [Fintype α] [DecidableEq α] [Fintype V] [DecidableEq V] (M : Matroid α) (hM : M.E = Set.univ) (cls : α → V) (c : α → ℝ)
    (I : Finset α) (hI : ExtremeP (matInd M) cls c I) (u : V) (P : List α)
    (hP : IsShortestAmong (IsAugPathFrom (matInd M) cls I u) c I P) :
    ∀ x ∈ P.dropLast, ¬ (x ∉ I ∧ matInd M (insert x I)) := by sorry

end MinCostArbPacking.Main
