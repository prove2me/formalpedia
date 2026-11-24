-- Prove2me | Theorems.Thm_GlobalTheory_Proof_ColumnMapShift_colMap_X
-- name    : GlobalTheory.Proof.ColumnMapShift.colMap_X
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:55:46.415377+00:00
-- url     : https://prove2.me/theorems/164fb244-0dfe-444a-9539-e132e29fc89c
-- title:
--   Column Map Shift: col Map X
-- statement:
--   The Column Map Shift construction uses the col Map X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ColumnMapShift.lean#L51-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ColumnMapShift.lean#L51-L53

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

theorem GlobalTheory.Proof.ColumnMapShift.colMap_X (g : T → Fin n → Fin n → k) (τ : T) (j : Fin (r τ)) (b : Fin n) :
    colMap r g (X ⟨τ, j, b⟩) = ∑ b', C (g τ b' b) * X (⟨τ, j, b'⟩ : Letter T r n) := by sorry
