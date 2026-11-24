-- Prove2me | Theorems.Thm_GlobalTheory_TorusNormal_cT_pm
-- name    : GlobalTheory.TorusNormal.cT_pm
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T16:10:15.76741+00:00
-- url     : https://prove2.me/theorems/d488a015-7b7b-4166-adb2-004eafb431a0
-- title:
--   Torus Normal: c T pm
-- statement:
--   The Torus Normal construction uses the c T pm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/UniformizerPowerTorusMemNormalUnitarySubgroup.lean#L31-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/UniformizerPowerTorusMemNormalUnitarySubgroup.lean#L31-L44

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

theorem GlobalTheory.TorusNormal.cT_pm {n : ℕ} (σ : L →+* L) (f g : Fin n → L) :
    cT σ (pm f g) = pm (fun i => σ (f i)) (fun i => σ (g (Fin.rev i))) := by sorry
