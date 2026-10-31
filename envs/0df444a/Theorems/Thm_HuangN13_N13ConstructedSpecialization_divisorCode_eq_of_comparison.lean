-- Prove2me | Theorems.Thm_HuangN13_N13ConstructedSpecialization_divisorCode_eq_of_comparison
-- name    : HuangN13.N13ConstructedSpecialization.divisorCode_eq_of_comparison
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T11:29:58.29299+00:00
-- url     : https://prove2.me/theorems/9b41f1ac-ed89-43b5-ae96-62ebd73f4dc2
-- title:
--   Coherently compared special divisors have equal code
-- statement:
--   The special divisor code agrees on two degree-two special divisors whenever their two-chart realizations are coherently compared.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/blob/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof/N13ConstructedSpecialization.lean. Exact flattened unit21 lines3998-4002, command SHA-256 02d65d6ce5dc367b7f1e35e40d282d595d5d72db75d2560bec991d5894964bf1. Original-file line mapping is not asserted.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_SpecialComparisonCore
import Definitions.Def_HuangN13_ComparisonOrdersCore

set_option autoImplicit false
open Polynomial

theorem HuangN13.N13ConstructedSpecialization.divisorCode_eq_of_comparison (D E : MazurProof.N13SpecialDivisorCharts.EffectiveDivisorTwo)
    (h : MazurProof.N13CoherentChartComparison.SpecialComparison (MazurProof.N13SpecialDivisorCharts.ofDivisor D) (MazurProof.N13SpecialDivisorCharts.ofDivisor E)) : MazurProof.N13SpecialAbelCode.divisorCode D = MazurProof.N13SpecialAbelCode.divisorCode E := by sorry
