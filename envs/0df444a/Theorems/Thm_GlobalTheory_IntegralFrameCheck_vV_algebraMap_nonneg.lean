-- Prove2me | Theorems.Thm_GlobalTheory_IntegralFrameCheck_vV_algebraMap_nonneg
-- name    : GlobalTheory.IntegralFrameCheck.vV_algebraMap_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:27:25.735078+00:00
-- url     : https://prove2.me/theorems/51829dbb-4383-400c-9c93-e72f9af4aa4d
-- title:
--   Integral Frame Check: v V algebra Map nonneg
-- statement:
--   The Integral Frame Check construction uses the v V algebra Map nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/VVAlgebraMapNonneg.lean#L16-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/VVAlgebraMapNonneg.lean#L16-L23

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllFree
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_VVAlgebraMapNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IntegralFrameCheck
open Formalism.L2.Pj NumberField IsDedekindDomain
open scoped WithZero
variable {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K'] [Algebra V K']
  [IsFractionRing V K']

theorem GlobalTheory.IntegralFrameCheck.vV_algebraMap_nonneg (a : V) : 0 ≤ vV V (algebraMap V K' a) := by sorry
