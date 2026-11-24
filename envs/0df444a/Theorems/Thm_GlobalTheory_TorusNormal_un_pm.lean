-- Prove2me | Theorems.Thm_GlobalTheory_TorusNormal_un_pm
-- name    : GlobalTheory.TorusNormal.un_pm
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:11:27.395797+00:00
-- url     : https://prove2.me/theorems/d585d7cf-76bb-479b-ae4f-22162f0ab519
-- title:
--   Torus Normal: un pm
-- statement:
--   The Torus Normal construction uses the un pm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/UniformizerPowerTorusMemNormalUnitarySubgroup.lean#L68-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/UniformizerPowerTorusMemNormalUnitarySubgroup.lean#L68-L74

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

theorem GlobalTheory.TorusNormal.un_pm {n : ℕ} (σ : L →+* L) (u : Fin n → L) (hσ : ∀ i, σ (u i) = -u i)
    (hsupp : ∀ i, u i ≠ 0 → 2 * i.val + 1 < n) : fIwasawaUn σ (pm 1 u) := by sorry
