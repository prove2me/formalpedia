-- Prove2me | Theorems.Thm_MultiAccessLogspace_Halting_lemma_3_4_failure_cover
-- name    : MultiAccessLogspace.Halting.lemma_3_4_failure_cover
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:40:07.828491+00:00
-- url     : https://prove2.me/theorems/e3052b0e-0d3e-44bf-b38b-9c6466aa10f6
-- title:
--   Lemma 3.4 — deterministic failure cover
-- statement:
--   Let $b\ge1$, and let $H_0,\ldots,H_{N-1}$ be arbitrary functions with values in $\mathbb N\cup\{\infty\}$ (no probability space is needed). For every $\omega$, if the list $(H_0(\omega),\ldots,H_{N-1}(\omega))$ is not a $(d,b)$-hyporuler, then at least one of the following holds:
--
--   1. some $H_i(\omega)$ lies outside $[d]=\{1,\ldots,d\}$;
--   2. for some coordinate $j$, the aggregate event $\operatorname{HasRepeatedBeforeGreater}(b,d,H,j)$ occurs: after choosing $h=H_j(\omega)\in[d]$, there is a greater-free interval ending at $j$ containing at least $b$ occurrences of $h$.
--
--   This is the deterministic event inclusion underlying Lemma 3.4. Condition 2 of Lemma 3.3 says precisely that, when all entries lie in $[d]$, failure of the hyporuler property produces the second alternative. Thus the lemma reduces the probability estimate to two finite union bounds.
--
--   **Formalization Note.** `Fin N` uses zero-based coordinates, whereas the paper numbers its coordinates from $1$ to $N$.
-- source:
--   William M. Hoza, STOC 2027 submission #92 (October 2026), Lemmas 3.3 and 3.4, PDF p. 7 (printed p. 6); the statement is the event-level union bound used in the proof of Lemma 3.4; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/92.pdf; PDF SHA-256 92de35889559d87b5a77d83317b9c7b2c8924912fbd5c712f2af3c005c8998d8

import Mathlib
import Definitions.Def_MultiAccessLogspace_Halting_Rulers
import Definitions.Def_MultiAccessLogspace_Halting_HyporulerEvents

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MultiAccessLogspace.Halting

/-- A non-hyporuler either has an entry outside `[d]`, or has a coordinate at which the
repeated-value event in the backward-scanning argument occurs. -/
theorem lemma_3_4_failure_cover {Ω : Type*} (d b N : ℕ) (hb : 1 ≤ b)
    (H : Fin N → Ω → ℕ∞) :
    {ω | ¬ IsHyporulerENat b d (List.ofFn fun i => H i ω)} ⊆
      (⋃ i, {ω | ¬ InRangeENat d (H i ω)}) ∪
        (⋃ j, {ω | HasRepeatedBeforeGreater b d H j ω}) := by sorry
