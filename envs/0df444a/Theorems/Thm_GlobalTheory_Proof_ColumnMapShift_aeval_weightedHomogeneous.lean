-- Prove2me | Theorems.Thm_GlobalTheory_Proof_ColumnMapShift_aeval_weightedHomogeneous
-- name    : GlobalTheory.Proof.ColumnMapShift.aeval_weightedHomogeneous
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:55:42.916311+00:00
-- url     : https://prove2.me/theorems/7e782c79-a617-479e-9a22-354712f2cde4
-- title:
--   Column Map Shift: aeval weighted Homogeneous
-- statement:
--   The Column Map Shift construction uses the aeval weighted Homogeneous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ColumnMapShift.lean#L12-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ColumnMapShift.lean#L12-L29

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

theorem GlobalTheory.Proof.ColumnMapShift.aeval_weightedHomogeneous {K σ τ : Type} [CommRing K] {w : σ → ℕ} {w' : τ → ℕ}
    {φ : MvPolynomial σ K} {m : ℕ} (hφ : IsWeightedHomogeneous w φ m)
    (v : σ → MvPolynomial τ K) (hv : ∀ i, IsWeightedHomogeneous w' (v i) (w i)) :
    IsWeightedHomogeneous w' (aeval v φ) m := by sorry
