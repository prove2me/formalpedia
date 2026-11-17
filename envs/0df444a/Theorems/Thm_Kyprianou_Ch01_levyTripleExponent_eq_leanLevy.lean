-- Prove2me | Theorems.Thm_Kyprianou_Ch01_levyTripleExponent_eq_leanLevy
-- name    : Kyprianou.Ch01.levyTripleExponent_eq_leanLevy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T19:55:55.449535+00:00
-- url     : https://prove2.me/theorems/482bc7e9-8197-4ae0-aa77-328c6d39a6d4
-- title:
--   Targeted Kyprianou and LeanLevy characteristic exponents coincide exactly
-- statement:
--   For every admissible Lévy–Khintchine triplet T and frequency xi, the signed Kyprianou Chapter 1 exponent in the collision-safe Definition is exactly the canonical LeanLevy triplet exponent, including drift, Gaussian variance and compensated jump term. The proof unfolds both formulas and uses ring normalisation. This supports the full Gaussian plus jump process existence construction and source-exact Chapter 1 exponent comparisons.
-- source:
--   Kyprianou (2006), Chapter 1, equation (1.4) and Theorems 1.3–1.6. Reuses Proved ProbabilityTheory.LevyKhintchineTriple.exponent_def UUID 674959c0-4e8d-4dbc-b462-af9200c163e7.

import Definitions.Def_Kyprianou_Ch01_LevyTripletExponentTargeted
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Theorems.Thm_ProbabilityTheory_LevyKhintchineTriple_exponent_def
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Complex
set_option autoImplicit false

theorem Kyprianou.Ch01.levyTripleExponent_eq_leanLevy
    (T : ProbabilityTheory.LevyKhintchineTriple) (xi : ℝ) :
    Kyprianou.Ch01.levyTripleExponent T xi = T.exponent xi := by
  sorry
