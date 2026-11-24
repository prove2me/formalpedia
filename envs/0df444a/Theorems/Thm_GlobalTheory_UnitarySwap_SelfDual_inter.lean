-- Prove2me | Theorems.Thm_GlobalTheory_UnitarySwap_SelfDual_inter
-- name    : GlobalTheory.UnitarySwap.SelfDual.inter
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T15:48:38.74943+00:00
-- url     : https://prove2.me/theorems/26995c4a-8b7d-495e-b351-dda950ff794b
-- title:
--   Self Dual: inter
-- statement:
--   The Self Dual construction uses the inter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/InvMemDoubleCosetAndComm.lean#L75-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/InvMemDoubleCosetAndComm.lean#L75-L90

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

theorem GlobalTheory.UnitarySwap.SelfDual.inter (h : SelfDual B W Λ) (hB : ∀ u v, σ (B u v) = B v u) {e f x y : V}
    (hx : ∀ v, B e v = 0 → B x v = 0) (hy : ∀ v, B f v = 0 → B y v = 0)
    (hdec : ∀ v ∈ Λ, ∃ c ∈ intL L, ∃ d ∈ intL L, ∃ v₀ ∈ Λ,
      B e v₀ = 0 ∧ B f v₀ = 0 ∧ v = c • x + d • y + v₀) :
    SelfDual B (perp B W e f) (Λ ∩ (perp B W e f : Set V)) := by sorry
