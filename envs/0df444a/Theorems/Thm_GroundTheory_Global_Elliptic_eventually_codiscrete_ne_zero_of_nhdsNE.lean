-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_eventually_codiscrete_ne_zero_of_nhdsNE
-- name    : GroundTheory.Global.Elliptic.eventually_codiscrete_ne_zero_of_nhdsNE
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:20:06.884547+00:00
-- url     : https://prove2.me/theorems/b872ee16-c7b0-4639-8f15-98523b7955f7
-- title:
--   Elliptic: eventually codiscrete ne zero of nhds NE
-- statement:
--   The Elliptic construction uses the eventually codiscrete ne zero of nhds NE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/EllipticRational.lean#L243-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/EllipticRational.lean#L243-L251

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticConstant
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set Polynomial
open scoped PeriodPair
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable {L : PeriodPair}

theorem GroundTheory.Global.Elliptic.eventually_codiscrete_ne_zero_of_nhdsNE {F : ℂ → ℂ} (hF : Meromorphic F)
    (h : ∀ᶠ z in 𝓝[≠] (0 : ℂ), F z ≠ 0) : ∀ᶠ z in codiscrete ℂ, F z ≠ 0 := by sorry
