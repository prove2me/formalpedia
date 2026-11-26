-- Prove2me | Theorems.Thm_Kyprianou_Ch05_smithFiniteMeanCompatibility
-- name    : Kyprianou.Ch05.smithFiniteMeanCompatibility
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T16:57:18.174686+00:00
-- url     : https://prove2.me/theorems/e41e0941-c03d-4182-bc53-eef9cfb3325e
-- title:
--   Chapter 5 Blackwell bridge: finite mean agrees with Smith's lower integral
-- statement:
--   For a nonnegative supported measure with integrable identity function, Smith's extended mean is the coercion of the ordinary real mean.
-- source:
--   Source-exact auxiliary bridge for Kyprianou (2006), Theorem 5.1(i), parent b176b15b-454a-4ba5-acbe-94ebda0502ec, to proved Smith (1955) Theorem A(a), 4723f731-2818-44df-bc1c-771b012557ba.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_SmithRegenerative_Equilibrium_Renewal
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- For a nonnegative supported measure with integrable identity function, Smith's extended mean is the coercion of the ordinary real mean. -/
theorem Kyprianou.Ch05.smithFiniteMeanCompatibility
    (F : Measure Real)
    (hSupport : F (Set.Iio (0 : Real)) = 0)
    (hFiniteMean : Integrable (fun x : Real => x) F) :
    SmithRegenerative.Equilibrium.mean F =
      ENNReal.ofReal (∫ x : Real, x ∂F) := by sorry
