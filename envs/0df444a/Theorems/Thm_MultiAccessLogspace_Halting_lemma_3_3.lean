-- Prove2me | Theorems.Thm_MultiAccessLogspace_Halting_lemma_3_3
-- name    : MultiAccessLogspace.Halting.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:59:23.449204+00:00
-- url     : https://prove2.me/theorems/7fab2991-b409-4c42-8cc4-c01838afd1bf
-- title:
--   Lemma 3.3 — characterizing hyporulers
-- statement:
--   Let $d\ge0$, $b\ge1$, and $h=(h_1,\ldots,h_N)$ be a list with every entry in $\{1,\ldots,d\}$. For $j\in\{1,\ldots,N\}$ let $i_j$ be the largest index at most $j$ whose entry exceeds $h_j$, or zero if there is no such index. Then
--   $$
--   h\text{ is a }(d,b)\text{-hyporuler}\quad\Longleftrightarrow\quad
--   \forall j\in\{1,\ldots,N\},\ \#\{k:i_j<k\le j,\ h_k=h_j\}\le b-1.
--   $$
--   This gives both directions of the local recognition criterion. At $d=0$ the domain condition forces the empty list.
--
--   Differences from the source:
--   - encoding: h ∈ [d]^N and the last larger index, defaulting to zero → a finite List ℕ with entries in 1..d and a Finset supremum over 1..j, defaulting to zero; reason: list length supplies N and the natural finite supremum gives exactly the specified default
-- source:
--   William M. Hoza, STOC 2027 submission #92 (October 2026), Lemma 3.3, PDF p. 7 (printed p. 6); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/92.pdf; PDF SHA-256 92de35889559d87b5a77d83317b9c7b2c8924912fbd5c712f2af3c005c8998d8

import Mathlib
import Definitions.Def_MultiAccessLogspace_Halting_Rulers

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MultiAccessLogspace.Halting

/-- Lemma 3.3 (Characterizing hyporulers). For `h ∈ [d]^N`, being a `(d, b)`-hyporuler is
equivalent to Condition 2. -/
theorem lemma_3_3 (d b : ℕ) (hb : 1 ≤ b) (h : List ℕ) (hd : ∀ a ∈ h, 1 ≤ a ∧ a ≤ d) :
    IsHyporuler b d h ↔ HyporulerCondition b h := by sorry

end MultiAccessLogspace.Halting
