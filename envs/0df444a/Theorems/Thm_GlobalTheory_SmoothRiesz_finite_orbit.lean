-- Prove2me | Theorems.Thm_GlobalTheory_SmoothRiesz_finite_orbit
-- name    : GlobalTheory.SmoothRiesz.finite_orbit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:06.066189+00:00
-- url     : https://prove2.me/theorems/aea03fc9-4ff0-4d9b-bfe4-e0903ebf337a
-- title:
--   Smooth Riesz: finite orbit
-- statement:
--   The Smooth Riesz construction uses the finite orbit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/UnitaryAdmissibleMatrixCoefficient.lean#L22-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/UnitaryAdmissibleMatrixCoefficient.lean#L22-L36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_LeviRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_UnitaryAdmissibleMatrixCoefficient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GodementJacquet MeasureTheory
open scoped Pointwise
open GlobalTheory GlobalTheory.SmoothRiesz

theorem GlobalTheory.SmoothRiesz.finite_orbit {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ G V) (hsm : IsSmooth σ)
    (K : Subgroup G) (hKc : IsCompact (K : Set G)) (y : V) :
    ((fun k : G => σ k y) '' (K : Set G)).Finite := by sorry
