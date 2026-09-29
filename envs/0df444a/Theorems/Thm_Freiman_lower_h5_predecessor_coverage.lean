-- Prove2me | Theorems.Thm_Freiman_lower_h5_predecessor_coverage
-- name    : Freiman.lower_h5_predecessor_coverage
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:53:09.261248+00:00
-- url     : https://prove2.me/theorems/b6ade30f-55e6-4772-ace1-40265234f37c
-- title:
--   Freiman p97: predecessor coverage
-- statement:
--   Exhaust the actual immediate predecessor using guarded physical additions: odd/odd10 without reflection, even/even10 or20 with reflection, or mixed21 with reflection. Initial depth is ruled out. Common odd parity is retained by ContextFits; only the23 printed source-cut cases are used.
-- source:
--   Freiman report, 'The carried target in the shortened-left case of Section 14', sec:h5-source-target, Lemma lem:h5-original-two (source printed p. 97), report/source/staging/parts/h5_target.tex; global_selection.tex priority rule; certificates/target_selection/h5_cases.json and h5_original_appendix_printed.json; verification/families/target_selection/verify_h5_original_independent.py.

import Definitions.Def_Freiman_lowerH5Verification
import Definitions.Def_Freiman_lowerInitialEntry
import Mathlib.Tactic

open Freiman

theorem Freiman.lower_h5_predecessor_coverage (hc : lowerH5CatalogValid)
    (hg : ∀ (p : LowerPair), lowerAdmissible p → ∀ l, lowerOffered p l → lowerGuardAllowed p l)
    (hi : ∀ (t : ℝ) (p : LowerPair), lowerInitialRoot t p → ¬(lowerMixed p ∧ lowerL p))
    (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n)
    (ha : lowerH5Active (h n)) (hr : ¬lowerEnds (lowerNormalize (h n)).2 [3]) :
    ∃ c ∈ lowerH5Cases, lowerH5Immediate h n c := by
  sorry
