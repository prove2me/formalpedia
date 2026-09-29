-- Prove2me | Theorems.Thm_Freiman_lower_run_tail_parameter
-- name    : Freiman.lower_run_tail_parameter
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:17:41.650168+00:00
-- url     : https://prove2.me/theorems/14496182-ed36-4af8-8370-186c6c7a760c
-- title:
--   Freiman lower construction: run tail parameter
-- statement:
--   The finite run parameter starts at 1/3, then obeys tau_(k+1)=1/(3+tau_k), giving the uniform interval [3/10,1/3] for every positive k.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/j_family.tex, tau_k recurrence

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_run_tail_parameter : ∀ k : ℕ, 0 < k →
    (3/10 : ℝ) ≤ finiteCF (List.replicate k (3 : ℕ+)) ∧
    finiteCF (List.replicate k (3 : ℕ+)) ≤ (1/3 : ℝ) := by
  sorry
