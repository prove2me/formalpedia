-- Prove2me | Theorems.Thm_Freiman_lower_run_parameter_transfer
-- name    : Freiman.lower_run_parameter_transfer
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:17:49.096917+00:00
-- url     : https://prove2.me/theorems/0f42d4b8-f39c-4bb9-99ff-ddd796ccc7b9
-- title:
--   Freiman lower construction: run parameter transfer
-- statement:
--   Exact matrix update sends (r,s,q) to (R_k,S_k,Q_k); the uniform tail-parameter box implies the stated Q bounds and preserves the original width orientation for all k, with ratio below 19/5.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/j_family.tex, eq:j3-updated-parameters and eq:j3-Q-box

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_run_parameter_transfer (htau : ∀ k : ℕ, 0 < k → (3/10 : ℝ) ≤ finiteCF (List.replicate k (3 : ℕ+)) ∧ finiteCF (List.replicate k (3 : ℕ+)) ≤ (1/3 : ℝ))
    (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hr : lowerRunOffered p) : lowerRunParameters p := by
  sorry
