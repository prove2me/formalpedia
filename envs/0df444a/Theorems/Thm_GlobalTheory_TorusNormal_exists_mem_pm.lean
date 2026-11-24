-- Prove2me | Theorems.Thm_GlobalTheory_TorusNormal_exists_mem_pm
-- name    : GlobalTheory.TorusNormal.exists_mem_pm
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:11:22.641506+00:00
-- url     : https://prove2.me/theorems/dd04cf8a-1a3b-4505-8fe7-0b8a765e81ee
-- title:
--   Torus Normal: exists mem pm
-- statement:
--   The Torus Normal construction uses the exists mem pm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/UniformizerPowerTorusMemNormalUnitarySubgroup.lean#L131-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/UniformizerPowerTorusMemNormalUnitarySubgroup.lean#L131-L170

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

theorem GlobalTheory.TorusNormal.exists_mem_pm (σ : L →+* L) {n : ℕ} (hσv : ∀ x, Valued.v (σ x) = Valued.v x)
    (N : Subgroup (GU σ n)) (hK : KU σ n ≤ N) (hU : ∀ u : GU σ n, IsUnipU u → u ∈ N)
    (y : Fin n → L) (hy0 : ∀ i, y i ≠ 0) (hyσ : ∀ i, σ (y i) = -y i) :
    ∃ g ∈ N, ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      pm (fun i => if 2 * i.val + 1 < n ∨ 2 * (Fin.rev i).val + 1 < n then 0 else 1)
        (fun i => (if 2 * i.val + 1 < n then y i else 0) +
          (if 2 * (Fin.rev i).val + 1 < n then -(y (Fin.rev i))⁻¹ else 0)) := by sorry
