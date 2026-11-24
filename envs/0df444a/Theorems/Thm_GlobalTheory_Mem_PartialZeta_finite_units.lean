-- Prove2me | Theorems.Thm_GlobalTheory_Mem_PartialZeta_finite_units
-- name    : GlobalTheory.Mem.PartialZeta.finite_units
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:22:51.141988+00:00
-- url     : https://prove2.me/theorems/271005d6-9b7e-4b75-b412-6f61a6233206
-- title:
--   Partial Zeta: finite units
-- statement:
--   The Partial Zeta construction uses the finite units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RayClassPartialZetaContinuation.lean#L33-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RayClassPartialZetaContinuation.lean#L33-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LatticeEpsteinZetaContinuationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayClassPartialZetaContinuation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.PartialZeta
variable {K : Type} [Field K] [NumberField K]

theorem GlobalTheory.Mem.PartialZeta.finite_units [IsTotallyComplex K] (h2 : Module.finrank ℚ K = 2) : Finite (𝓞 K)ˣ := by sorry
