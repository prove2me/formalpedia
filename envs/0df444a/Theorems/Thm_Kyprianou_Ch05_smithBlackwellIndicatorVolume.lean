-- Prove2me | Theorems.Thm_Kyprianou_Ch05_smithBlackwellIndicatorVolume
-- name    : Kyprianou.Ch05.smithBlackwellIndicatorVolume
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T16:57:23.761515+00:00
-- url     : https://prove2.me/theorems/df951c98-2a4a-5553-a7dd-59f38d5277df
-- title:
--   Chapter 5 Blackwell bridge: Lebesgue integral of half-open indicator
-- statement:
--   Integrating the indicator of [0,y) on the positive half-line gives its length y.
-- source:
--   Source-exact auxiliary bridge for Kyprianou (2006), Theorem 5.1(i), parent b176b15b-454a-4ba5-acbe-94ebda0502ec, to proved Smith (1955) Theorem A(a), 4723f731-2818-44df-bc1c-771b012557ba.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_SmithRegenerative_Equilibrium_Renewal
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Integrating the indicator of [0,y) on the positive half-line gives its length y. -/
theorem Kyprianou.Ch05.smithBlackwellIndicatorVolume
    (y : Real) (hy : 0 < y) :
    (∫ v in Set.Ioi 0, (Set.Ico 0 y).indicator (fun _ : Real => (1 : Real)) v) = y := by sorry
