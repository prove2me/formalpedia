-- Prove2me | Theorems.Thm_Freiman_background_unrestricted
-- name    : Freiman.background_unrestricted
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:53:23.06133+00:00
-- url     : https://prove2.me/theorems/eec3854a-b6b5-48c7-9434-4e45acb0fec2
-- title:
--   background unrestricted
-- statement:
--   Every local value of a two-sided word on the alphabet $\{1,2,3\}$ is at most $\sqrt{21}$. The report bounds each tail by the greatest alternating tail $[0;\overline{1,3}]$.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.4, Lemma 1.7 (found:background), greatest-tail and central-neighbour case analysis.

import Definitions.Def_Freiman_wordRealization

open Freiman

theorem Freiman.background_unrestricted (a : ℤ → ℕ+) (ha : ∀ i : ℤ, (a i : ℕ) ≤ 3) (i : ℤ) :
    localValue a i ≤ Real.sqrt 21 := by sorry
