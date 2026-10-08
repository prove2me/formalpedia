-- Prove2me | Theorems.Thm_FuzzyGames_Walras_zero_not_mem_convexHull_Q
-- name    : FuzzyGames.Walras.zero_not_mem_convexHull_Q
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:07:04.029058+00:00
-- url     : https://prove2.me/theorems/badc7ca0-b36a-4d95-a297-4413d87a8cf0
-- title:
--   Proof of Theorem 4.1 — if x̄ is in the fuzzy core then 0 ∉ co(⋃ᵢ Q(i))
-- statement:
--   Let an exchange economy satisfy the assumptions of §4 and let $\bar x$ belong to its fuzzy core. With
--   $Q(i) = Y(i) - \{x^i \in \mathbb{R}^l_+ : x^i \succ_i \bar x^i\}$ for $i = 1,\dots,n$,
--   $$0 \notin \operatorname{co}\Big(\bigcup_{i=1}^n Q(i)\Big),$$
--   where $\operatorname{co}$ denotes the convex hull in $\mathbb{R}^l$.
--
--   This is the step of the proof of Theorem 4.1 that converts membership in the fuzzy core into a convex-geometric statement: a convex combination of elements of the $Q(i)$ equal to $0$ would describe a fuzzy coalition, with the weights as rates of participation, that improves upon $\bar x$. The separation theorem is then applied to this convex set to produce the equilibrium price.
--
--   **Formalization Note.** The convex hull is Mathlib's `convexHull ℝ`.
-- source:
--   Aubin, Cooperative Fuzzy Games, Math. Oper. Res. 6(1) (1981), proof of Theorem 4.1, p. 6

import Mathlib
import Definitions.Def_FuzzyGames_Walras_Basic

namespace FuzzyGames.Walras

/-- Proof of Theorem 4.1 (Aubin 1981, p. 6): if `x̄` belongs to the fuzzy core, then
`0 ∉ co(⋃ᵢ Q(i))`. -/
theorem zero_not_mem_convexHull_Q {n l : ℕ} (E : Economy n l) (hE : E.Assumptions)
    (xbar : Fin n → Fin l → ℝ) (hx : xbar ∈ E.fuzzyCore) :
    (0 : Fin l → ℝ) ∉ convexHull ℝ (⋃ i, E.Q xbar i) := by sorry

end FuzzyGames.Walras
