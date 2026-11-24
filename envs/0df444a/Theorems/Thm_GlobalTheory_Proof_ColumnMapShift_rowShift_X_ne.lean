-- Prove2me | Theorems.Thm_GlobalTheory_Proof_ColumnMapShift_rowShift_X_ne
-- name    : GlobalTheory.Proof.ColumnMapShift.rowShift_X_ne
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:56:01.4247+00:00
-- url     : https://prove2.me/theorems/2591911e-b004-4412-a550-e86b7965d612
-- title:
--   Column Map Shift: row Shift X ne
-- statement:
--   The Column Map Shift construction uses the row Shift X ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ColumnMapShift.lean#L43-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ColumnMapShift.lean#L43-L49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_UnitaryDetClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ColumnMapShift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Proof GlobalTheory.Proof.ColumnMapShift
open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {T : Type} {r : T → ℕ} {n : ℕ} {k : Type} [Field k]

theorem GlobalTheory.Proof.ColumnMapShift.rowShift_X_ne (σ : T) (i i' : Fin (r σ)) (t : k) (τ : T) (j : Fin (r τ))
    (h : (⟨τ, j⟩ : Σ s, Fin (r s)) ≠ ⟨σ, i⟩) (b : Fin n) :
    rowShift r n k σ i i' t (X ⟨τ, j, b⟩) = X ⟨τ, j, b⟩ := by sorry
