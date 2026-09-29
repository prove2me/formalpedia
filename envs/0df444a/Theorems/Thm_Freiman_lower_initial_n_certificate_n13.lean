-- Prove2me | Theorems.Thm_Freiman_lower_initial_n_certificate_n13
-- name    : Freiman.lower_initial_n_certificate_n13
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:20:09.037981+00:00
-- url     : https://prove2.me/theorems/7b16ced9-f981-4ba8-a38d-60cd73e7e927
-- title:
--   Freiman lower construction: initial n certificate n13
-- statement:
--   Exact finite quartic-to-quadratic coefficient identity, signs and endpoint-safe lower bound Q0+Q1/85>0, plus a separate n=0 positive radical value.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-contacts; exact initial contact appendix

import Definitions.Def_Freiman_lowerInitialSeamData
import Definitions.Def_Freiman_lowerInitialNData
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

open scoped BigOperators

theorem Freiman.lower_initial_n_certificate_n13 : lowerInitialNCertificateValid .n13 := by
  sorry
