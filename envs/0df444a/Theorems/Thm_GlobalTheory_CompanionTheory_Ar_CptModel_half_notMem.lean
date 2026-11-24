-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CptModel_half_notMem
-- name    : GlobalTheory.CompanionTheory.Ar.CptModel.half_notMem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:57:22.622708+00:00
-- url     : https://prove2.me/theorems/16c7184b-f913-41cd-a232-8769b2b948ab
-- title:
--   Cpt Model: half not Mem
-- statement:
--   The Cpt Model construction uses the half not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/InjectiveOfIsCptGen.lean#L169-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/InjectiveOfIsCptGen.lean#L169-L178

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsCptGen
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InjectiveOfIsCptGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.CptModel
open AlgebraicGeometry CategoryTheory

theorem GlobalTheory.CompanionTheory.Ar.CptModel.half_notMem : (2 : ℚ)⁻¹ ∉ regAt _ two := by sorry
