-- Prove2me | Theorems.Thm_GlobalTheory_WeilM_diag_invariant_comp
-- name    : GlobalTheory.WeilM.diag_invariant_comp
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:55:20.483312+00:00
-- url     : https://prove2.me/theorems/43ec96a8-46a6-4f0b-845b-85b84d2b904d
-- title:
--   Weil M: diag invariant comp
-- statement:
--   The Weil M construction uses the diag invariant comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeilObjectsInhabited.lean#L38-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeilObjectsInhabited.lean#L38-L120

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSplittingSplitOm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompactOpenAddSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeilObjectsInhabited
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ValuativeRel
open scoped NNReal Topology Kronecker
open GlobalTheory GlobalTheory.WeilM
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {α β κ : Type}

theorem GlobalTheory.WeilM.diag_invariant_comp [Invertible (2 : F)] [Fintype κ] [DecidableEq κ] (ψ : AddChar F ℂ) (hψ : Continuous ψ)
    (hψ1 : ψ ≠ 1) (l : ((κ ⊕ κ → F) → ℂ) →ₗ[ℂ] ℂ)
    (hl : ∀ x y : κ → F, ∀ φ ∈ SB (κ ⊕ κ → F), l (schr ψ (Sum.elim x x, Sum.elim y (-y)) φ) = l φ)
    (g : GL κ F) {φ φ' : (κ ⊕ κ → F) → ℂ} (hφ : φ ∈ SB (κ ⊕ κ → F)) (hφ' : φ' ∈ SB (κ ⊕ κ → F))
    (h : ∀ x, φ' (Sum.elim x x) = φ (Sum.elim (g.val.mulVec x) (g.val.mulVec x))) :
    ((distribHaarChar F (GeneralLinearGroup.det g) : ℝ) : ℂ) * l φ' = l φ := by sorry
