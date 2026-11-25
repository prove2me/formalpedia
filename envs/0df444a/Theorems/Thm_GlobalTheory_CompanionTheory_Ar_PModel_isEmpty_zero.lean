-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PModel_isEmpty_zero
-- name    : GlobalTheory.CompanionTheory.Ar.PModel.isEmpty_zero
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:00:25.729812+00:00
-- url     : https://prove2.me/theorems/84636b57-1aab-4442-a152-01fffaf2714c
-- title:
--   PModel: is Empty zero
-- statement:
--   The PModel construction uses the is Empty zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/GlueApplyOfNotInFibre.lean#L43-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/GlueApplyOfNotInFibre.lean#L43-L47

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsGenOfIsVBOne
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_StalkClosedPointToToStalk
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_GlueApplyOfNotInFibre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar
open AlgebraicGeometry CategoryTheory

theorem GlobalTheory.CompanionTheory.Ar.PModel.isEmpty_zero (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) :
    IsEmpty (PModel o (0 : κ → Ω)) := by sorry
