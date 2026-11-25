-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_FormalGroupTorsionCharts_tateModule_ker
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.FormalGroupTorsionCharts.tateModule_ker
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:09:14.842937+00:00
-- url     : https://prove2.me/theorems/01f30d06-952b-5abf-8d43-1b85f682d421
-- title:
--   Formal Group Torsion Charts: tate Module ker
-- statement:
--   The Formal Group Torsion Charts construction uses the tate Module ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/PoincareCuspForms/FormalGroupTorsionCharts.lean#L179-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/PoincareCuspForms/FormalGroupTorsionCharts.lean#L179-L191

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_HtLinStatement
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_FormalGroupTorsionCharts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsLocalRing TensorProduct ReciprocityTheory.PGsh
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.FormalGroupTorsionCharts
universe u v
variable {R₀ : Type u} [CommRing R₀]
variable {k : LAlg R₀}

theorem GlobalTheory.IndefiniteRowSideFullHecke.FormalGroupTorsionCharts.tateModule_ker (B : BX R₀) (p : ℕ) (O : LAlg R₀) (τ : ℕ → B.G O)
    (hτ : τ ∈ tateModule B p O) : τ 0 = 0 ↔ ∃ τ' ∈ tateModule B p O, τ = p • τ' := by sorry
