-- Prove2me | Theorems.Thm_GlobalTheory_MainToRows_hRows_eq
-- name    : GlobalTheory.MainToRows.hRows_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:26:35.679797+00:00
-- url     : https://prove2.me/theorems/94b314f0-1040-4cc2-a385-8067daddeeb9
-- title:
--   Main To Rows: h Rows eq
-- statement:
--   The Main To Rows construction uses the h Rows eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/MainTermImpliesRowHypothesis.lean#L89-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/MainTermImpliesRowHypothesis.lean#L89-L96

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MainTermImpliesRowHypothesis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds
noncomputable section
open scoped BigOperators
open Classical MvPowerSeries Formalism.IncomingBounds Formalism.UnitaryBoundIntegral
open GlobalTheory GlobalTheory.MainToRows
variable {C : Type} [Field C]

theorem GlobalTheory.MainToRows.hRows_eq (n0 : ℕ) (H : MvPowerSeries (Fin n0 ⊕ Fin n0) C) :
    hRows n0 H = ∑ ρ : Fin n0, rename (rowE ρ) H := by sorry
