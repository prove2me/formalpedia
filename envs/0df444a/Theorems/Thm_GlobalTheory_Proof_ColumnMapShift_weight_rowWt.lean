-- Prove2me | Theorems.Thm_GlobalTheory_Proof_ColumnMapShift_weight_rowWt
-- name    : GlobalTheory.Proof.ColumnMapShift.weight_rowWt
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:55:56.680034+00:00
-- url     : https://prove2.me/theorems/61d55353-3d58-45f7-8058-305955b0dc2c
-- title:
--   Column Map Shift: weight row Wt
-- statement:
--   The Column Map Shift construction uses the weight row Wt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ColumnMapShift.lean#L80-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ColumnMapShift.lean#L80-L91

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

theorem GlobalTheory.Proof.ColumnMapShift.weight_rowWt [Fintype T] (σ : T) (i : Fin (r σ)) (m : Letter T r n →₀ ℕ) :
    Finsupp.weight (rowWt n σ i) m = ∑ b : Fin n, m ⟨σ, i, b⟩ := by sorry
