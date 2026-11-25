-- Prove2me | Theorems.Thm_GlobalTheory_CoeffExt_descend_bound
-- name    : GlobalTheory.CoeffExt.descend_bound
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:58:48.373329+00:00
-- url     : https://prove2.me/theorems/1fa0e1d9-3dbd-40e0-b6c3-86ebe90be57b
-- title:
--   Coeff Ext: descend bound
-- statement:
--   The Coeff Ext construction uses the descend bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/MemFiniteCocyclesIffBcrisTensorCoboundary.lean#L536-L563
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/MemFiniteCocyclesIffBcrisTensorCoboundary.lean#L536-L563

import Mathlib
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MemFiniteCocyclesIffBcrisTensorCoboundary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CoeffExt
open Formalism.WeaklyAdmissibleFiltrations TensorProduct Module

theorem GlobalTheory.CoeffExt.descend_bound {m k f : ℕ∞} {m' k' d : ℕ} (hd : 0 < d) (hf : f ≠ ⊤)
    (hm : (m' : ℕ∞) * f = d * m) (hk : (k' : ℕ∞) * f = d * k) {β : ℝ} (h : (m' : ℝ) ≤ β * k') :
    ∃ a c : ℕ, m = a ∧ k = c ∧ (a : ℝ) ≤ β * c := by sorry
