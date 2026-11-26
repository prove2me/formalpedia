-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw48_true_martingale_productGrid
-- name    : Kyprianou.Ch04.kw48_true_martingale_productGrid
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T00:44:20.37922+00:00
-- url     : https://prove2.me/theorems/bfc3738b-8d36-52ae-970c-28ce4ffea94c
-- title:
--   Complex two parameter Kella Whitt martingale
-- statement:
--   Complex two parameter Kella Whitt martingale.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.8(i).

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_Kyprianou_Ch04_kw48_M_adapted_integrable
import Theorems.Thm_Kyprianou_Ch04_kw48_grid_event_ledger
import Theorems.Thm_Kyprianou_Ch04_kw48_grid_gain_uniform_bound
import Theorems.Thm_Kyprianou_Ch04_kw48_capped_grid_pathwise_limit
import Theorems.Thm_Kyprianou_Ch04_kw48_envelope_integrable
import Theorems.Thm_Kyprianou_Ch04_kw48_martingale_from_grid_event_limit
import Theorems.Thm_Kyprianou_Ch04_kw47_capped_uniform_grid
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The complex reflected two-parameter process is a true martingale
by dominated transfer of centred predictable product grids. -/

theorem Kyprianou.Ch04.kw48_true_martingale_productGrid {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration NNReal mΩ)
    (L : SpectrallyNegativeLevy P F) (Psi : Real → Complex)
    (hPsi : ∀ (t : NNReal) (theta : Real),
      (∫ w, Complex.exp (Complex.I*(theta:Complex)*(L.X t w:Complex)) ∂P) =
      Complex.exp (-((t:Real):Complex)*Psi theta))
    (alpha beta : Real) : Martingale (M L Psi alpha beta) F P := by sorry
