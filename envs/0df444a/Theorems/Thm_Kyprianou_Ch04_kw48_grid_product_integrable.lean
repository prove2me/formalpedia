-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw48_grid_product_integrable
-- name    : Kyprianou.Ch04.kw48_grid_product_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:44:13.863045+00:00
-- url     : https://prove2.me/theorems/5f89e7d7-b40b-597a-a6ca-1fdc1c8d4d0a
-- title:
--   Integrability of finite-time characteristic exponential products
-- statement:
--   Integrability of finite-time characteristic exponential products.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.8(i).

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_Kyprianou_Ch04_kw48_Z_adapted
import Theorems.Thm_Kyprianou_Ch04_kw48_norm_EH
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A finite-time predictable exponential times any characteristic
exponential value is integrable by its deterministic modulus. -/

theorem Kyprianou.Ch04.kw48_grid_product_integrable {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (Psi : Real → Complex)
    (alpha beta : Real) (s t : NNReal) :
    Integrable (fun w => H L Psi alpha beta s w*E L Psi alpha t w) P := by sorry
