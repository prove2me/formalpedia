-- Prove2me | Theorems.Thm_GlobalTheory_TorusNormal_unip_pm
-- name    : GlobalTheory.TorusNormal.unip_pm
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:23:40.03181+00:00
-- url     : https://prove2.me/theorems/d27eb587-4b2f-4ad8-a059-5494c0a8ee00
-- title:
--   Torus Normal: unip pm
-- statement:
--   The Torus Normal construction uses the unip pm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/UniformizerPowerTorusMemNormalUnitarySubgroup.lean#L76-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/UniformizerPowerTorusMemNormalUnitarySubgroup.lean#L76-L100

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

theorem GlobalTheory.TorusNormal.unip_pm {n : ℕ} (σ : L →+* L) (u : Fin n → L) (h : fIwasawaUn σ (pm 1 u))
    (hsupp : ∀ i, u i ≠ 0 → 2 * i.val + 1 < n) : IsUnipU (fIwasawaMk σ (pm 1 u) h) := by sorry
