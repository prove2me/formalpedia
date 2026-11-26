-- Prove2me | Theorems.Thm_Kyprianou_Ch05_smithBlackwellIndicatorIntervalIntegral
-- name    : Kyprianou.Ch05.smithBlackwellIndicatorIntervalIntegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T16:57:21.055572+00:00
-- url     : https://prove2.me/theorems/b285bded-dd1f-5944-b37e-237f71475837
-- title:
--   Chapter 5 Blackwell bridge: translated indicator integral equals renewal interval mass
-- statement:
--   For a real measure V and x nonnegative, the Stieltjes integral of the translated [0,y) indicator on [0,x+y] is the real mass of the interval (x,x+y]. This preserves the endpoint convention even if V has atoms.
-- source:
--   Source-exact auxiliary bridge for Kyprianou (2006), Theorem 5.1(i), parent b176b15b-454a-4ba5-acbe-94ebda0502ec, to proved Smith (1955) Theorem A(a), 4723f731-2818-44df-bc1c-771b012557ba.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_SmithRegenerative_Equilibrium_Renewal
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- For a real measure V and x nonnegative, the Stieltjes integral of the translated [0,y) indicator on [0,x+y] is the real mass of the interval (x,x+y]. This preserves the endpoint convention even if V has atoms. -/
theorem Kyprianou.Ch05.smithBlackwellIndicatorIntervalIntegral
    (V : Measure Real) (x y : Real) (hx : 0 ≤ x) :
    (∫ s in Set.Icc 0 (x+y),
      (Set.Ico 0 y).indicator (fun _ : Real => (1 : Real)) (x+y-s) ∂V) =
      (V (Set.Ioc x (x+y))).toReal := by sorry
