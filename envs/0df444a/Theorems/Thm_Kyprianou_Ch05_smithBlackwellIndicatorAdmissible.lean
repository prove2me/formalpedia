-- Prove2me | Theorems.Thm_Kyprianou_Ch05_smithBlackwellIndicatorAdmissible
-- name    : Kyprianou.Ch05.smithBlackwellIndicatorAdmissible
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T16:57:19.335293+00:00
-- url     : https://prove2.me/theorems/42869e27-7cab-550d-b2e5-73e0f6288cdb
-- title:
--   Chapter 5 Blackwell bridge: interval indicator admissible for Smith A(a)
-- statement:
--   The indicator of the half-open interval [0,y) is measurable, bounded on the positive half-line, nonincreasing there and integrable there, as required by Smith's Theorem A(a).
-- source:
--   Source-exact auxiliary bridge for Kyprianou (2006), Theorem 5.1(i), parent b176b15b-454a-4ba5-acbe-94ebda0502ec, to proved Smith (1955) Theorem A(a), 4723f731-2818-44df-bc1c-771b012557ba.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_SmithRegenerative_Equilibrium_Renewal
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- The indicator of the half-open interval [0,y) is measurable, bounded on the positive half-line, nonincreasing there and integrable there, as required by Smith's Theorem A(a). -/
theorem Kyprianou.Ch05.smithBlackwellIndicatorAdmissible
    (y : Real) (hy : 0 < y) :
    let psi : Real → Real := (Set.Ico 0 y).indicator (fun _ => 1)
    Measurable psi ∧ (∃ C : Real, ∀ v : Real, 0 ≤ v → |psi v| ≤ C) ∧
      AntitoneOn psi (Set.Ioi 0) ∧ IntegrableOn psi (Set.Ioi 0) := by sorry
