-- Prove2me | Theorems.Thm_Kyprianou_Ch05_smithZeroDelayRenewalIdentity
-- name    : Kyprianou.Ch05.smithZeroDelayRenewalIdentity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T16:57:13.475078+00:00
-- url     : https://prove2.me/theorems/a21bb764-9d44-56f1-9f1b-6d83c21b79b9
-- title:
--   Chapter 5 Blackwell bridge: zero-delay renewal measures coincide
-- statement:
--   Smith's renewal measure with zero initial delay is exactly the Chapter 5 renewal measure, including the zeroth convolution power.
-- source:
--   Source-exact auxiliary bridge for Kyprianou (2006), Theorem 5.1(i), parent b176b15b-454a-4ba5-acbe-94ebda0502ec, to proved Smith (1955) Theorem A(a), 4723f731-2818-44df-bc1c-771b012557ba.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_SmithRegenerative_Equilibrium_Renewal
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Smith's renewal measure with zero initial delay is exactly the Chapter 5 renewal measure, including the zeroth convolution power. -/
theorem Kyprianou.Ch05.smithZeroDelayRenewalIdentity
    (F : Measure Real) [IsProbabilityMeasure F] :
    SmithRegenerative.Equilibrium.renewalMeasure (Measure.dirac 0) F =
      renewalMeasure F := by sorry
