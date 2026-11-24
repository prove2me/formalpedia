-- Prove2me | Theorems.Thm_GlobalTheory_TorusNormal_idx_cases
-- name    : GlobalTheory.TorusNormal.idx_cases
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T16:08:27.642056+00:00
-- url     : https://prove2.me/theorems/b2b2bc0e-9533-47c8-aa80-9f5421ba10bd
-- title:
--   Torus Normal: idx cases
-- statement:
--   The Torus Normal construction uses the idx cases property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/UniformizerPowerTorusMemNormalUnitarySubgroup.lean#L117-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/UniformizerPowerTorusMemNormalUnitarySubgroup.lean#L117-L129

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
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem GlobalTheory.TorusNormal.idx_cases {n : ℕ} (i : Fin n) :
    (2 * i.val + 1 < n ∧ ¬ 2 * (Fin.rev i).val + 1 < n) ∨
    (¬ 2 * i.val + 1 < n ∧ 2 * (Fin.rev i).val + 1 < n) ∨
    (¬ 2 * i.val + 1 < n ∧ ¬ 2 * (Fin.rev i).val + 1 < n ∧ Fin.rev i = i) := by sorry
