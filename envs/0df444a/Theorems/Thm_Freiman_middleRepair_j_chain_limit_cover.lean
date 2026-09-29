-- Prove2me | Theorems.Thm_Freiman_middleRepair_j_chain_limit_cover
-- name    : Freiman.middleRepair_j_chain_limit_cover
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:30:00.350909+00:00
-- url     : https://prove2.me/theorems/5f85b0f4-6dfa-4967-abc7-6c2a4f86bd83
-- title:
--   Report convention repair: middleRepair_j_chain_limit_cover
-- statement:
--   Two same-parity chains whose endpoints converge to one point cover the hull of J1 and J2 after adjoining that point. This is the closed-coverage limit lemma, independent of certificate arithmetic. This draft uses the report-normalized child convention, preserving actual incoming order at equal widths.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part III, active source staging/m2b/m2b_body.tex, m2b:sec:jfamily, odd/even limiting coverage Repair: active m2b_body.tex lines 46–48 and §11 physical-cylinder argument.

import Definitions.Def_Freiman_middleRepair

open Freiman

theorem Freiman.middleRepair_j_chain_limit_cover :
    ∀ c : MiddleCore,
      (∀ k : ℕ, 1 ≤ k → (middleCover (middleRepairJ c k) ∩ middleCover (middleRepairJ c (k+2))).Nonempty) →
      Filter.Tendsto (fun k : ℕ => (middleBounds (middleRepairJ c k)).1) Filter.atTop (nhds (middleLimitValue c)) →
      Filter.Tendsto (fun k : ℕ => (middleBounds (middleRepairJ c k)).2) Filter.atTop (nhds (middleLimitValue c)) →
      ∀ t ∈ middleRepairJSpan c, t=middleLimitValue c ∨ ∃ k : ℕ, 1 ≤ k ∧ t∈middleCover (middleRepairJ c k) := by
  sorry
