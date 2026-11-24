-- Prove2me | Theorems.Thm_GlobalTheory_UnitarySwap_SelfDual_pair
-- name    : GlobalTheory.UnitarySwap.SelfDual.pair
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T15:46:40.270171+00:00
-- url     : https://prove2.me/theorems/66b46bc0-158e-4624-bf21-f237de3ce473
-- title:
--   Self Dual: pair
-- statement:
--   The Self Dual construction uses the pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/InvMemDoubleCosetAndComm.lean#L48-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/InvMemDoubleCosetAndComm.lean#L48-L49

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ImportsTail
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_InvMemDoubleCosetAndComm
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
open GlobalTheory GlobalTheory.UnitarySwap
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
variable {V : Type} [AddCommGroup V] [Module L V] {σ : L →+* L}
variable {B : V →ₛₗ[σ] V →ₗ[L] L} {W : Submodule L V} {Λ : Set V}

theorem GlobalTheory.UnitarySwap.SelfDual.pair (h : SelfDual B W Λ) {u v : V} (hu : u ∈ Λ) (hv : v ∈ Λ) : B u v ∈ intL L := by sorry
