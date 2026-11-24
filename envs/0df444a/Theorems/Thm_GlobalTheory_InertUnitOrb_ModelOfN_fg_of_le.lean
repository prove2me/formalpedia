-- Prove2me | Theorems.Thm_GlobalTheory_InertUnitOrb_ModelOfN_fg_of_le
-- name    : GlobalTheory.InertUnitOrb.ModelOfN.fg_of_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:15:50.398532+00:00
-- url     : https://prove2.me/theorems/2bd33367-2958-4ea7-aed6-308fb63a78b8
-- title:
--   Model Of N: fg of le
-- statement:
--   The Model Of N construction uses the fg of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsHermitianModelOfNormNeZero.lean#L157-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsHermitianModelOfNormNeZero.lean#L157-L161

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InertPlaceKappaOrbitalUnitEqSignedLatticeSumImpo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticNormsTraceUniformizerFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHermitianModelOfNormNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial Matrix
noncomputable section
open GlobalTheory GlobalTheory.InertUnitOrb GlobalTheory.InertUnitOrb.ModelOfN
variable {K : UQ}

theorem GlobalTheory.InertUnitOrb.ModelOfN.fg_of_le {V : Type} [AddCommGroup V] [Module K.O V] (L N : Submodule K.O V) (hfg : L.FG) (hle : N ≤ L) :
    N.FG := by sorry
