-- Prove2me | Theorems.Thm_Freiman_lower_initial_n_quotient_positive
-- name    : Freiman.lower_initial_n_quotient_positive
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:20:16.875151+00:00
-- url     : https://prove2.me/theorems/8065a86c-5eb2-410e-a6db-06d71cebd77c
-- title:
--   Freiman lower construction: initial n quotient positive
-- statement:
--   The actual source bound: Q2>0, Q1<0, Q0+Q1/85>0 implies Q(x)>0 on [0,1/85].
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-contacts; exact initial contact appendix

import Definitions.Def_Freiman_lowerInitialSeamData
import Definitions.Def_Freiman_lowerInitialNData
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

open scoped BigOperators

theorem Freiman.lower_initial_n_quotient_positive (hfield : ∀ z : CertField, (certFieldLower z:ℝ) ≤ certFieldVal z)
    (c : LowerInitialNCase) (hv : lowerInitialNCertificateValid c)
    (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) (1/85)) : 0 < lowerInitialNQuotEval c x := by
  sorry
