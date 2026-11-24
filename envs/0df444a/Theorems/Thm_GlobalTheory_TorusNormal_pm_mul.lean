-- Prove2me | Theorems.Thm_GlobalTheory_TorusNormal_pm_mul
-- name    : GlobalTheory.TorusNormal.pm_mul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T16:06:09.915328+00:00
-- url     : https://prove2.me/theorems/c75e7656-36a1-4f03-97f6-e3ff3a16eb00
-- title:
--   Torus Normal: pm mul
-- statement:
--   The Torus Normal construction uses the pm mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/UniformizerPowerTorusMemNormalUnitarySubgroup.lean#L19-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/UniformizerPowerTorusMemNormalUnitarySubgroup.lean#L19-L29

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawa
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_InvMemDoubleCosetAndComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_UniformizerPowerTorusMemNormalUnitarySubgroup
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG Matrix
noncomputable section
open GlobalTheory GlobalTheory.TorusNormal
open Formalism.UG.P
variable {L : Type} [Field L]

theorem GlobalTheory.TorusNormal.pm_mul {n : ℕ} (f g f' g' : Fin n → L) :
    pm f g * pm f' g' = pm (fun i => f i * f' i + g i * g' (Fin.rev i))
      (fun i => f i * g' i + g i * f' (Fin.rev i)) := by sorry
