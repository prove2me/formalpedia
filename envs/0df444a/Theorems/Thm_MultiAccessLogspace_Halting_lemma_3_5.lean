-- Prove2me | Theorems.Thm_MultiAccessLogspace_Halting_lemma_3_5
-- name    : MultiAccessLogspace.Halting.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:59:38.208424+00:00
-- url     : https://prove2.me/theorems/78c1b3ac-6940-46b8-8505-0a8330cba5ad
-- title:
--   Lemma 3.5 — hyporuler length bound
-- statement:
--   Let $d\ge0$, $b\ge1$, and let $h$ be a finite list of natural numbers of length $N$. If $h$ is a $(d,b)$-hyporuler, then
--   $$
--   N\le b^d-1.
--   $$
--   This bounds every valid hyporuler, including depth zero, where $N=0$. Since $b\ge1$, the power $b^d$ is at least one, so the natural subtraction agrees with the displayed integer bound. The bound supplies deterministic finiteness for the timer.
--
--   Differences from the source:
--   - encoding: h ∈ ℕ^N → a finite List ℕ with N given by its length; reason: the list represents exactly the finite sequence in the statement
-- source:
--   William M. Hoza, STOC 2027 submission #92 (October 2026), Lemma 3.5, PDF p. 8 (printed p. 7); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/92.pdf; PDF SHA-256 92de35889559d87b5a77d83317b9c7b2c8924912fbd5c712f2af3c005c8998d8

import Mathlib
import Definitions.Def_MultiAccessLogspace_Halting_Rulers

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MultiAccessLogspace.Halting

/-- Lemma 3.5 (Hyporuler length bound). -/
theorem lemma_3_5 (d b : ℕ) (hb : 1 ≤ b) (h : List ℕ) (hh : IsHyporuler b d h) :
    h.length ≤ b ^ d - 1 := by sorry

end MultiAccessLogspace.Halting
