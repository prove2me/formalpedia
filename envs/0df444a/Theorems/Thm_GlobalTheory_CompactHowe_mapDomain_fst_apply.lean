-- Prove2me | Theorems.Thm_GlobalTheory_CompactHowe_mapDomain_fst_apply
-- name    : GlobalTheory.CompactHowe.mapDomain_fst_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:54:21.320567+00:00
-- url     : https://prove2.me/theorems/7f8cc067-03c0-4e22-9659-34453a8e88a5
-- title:
--   Compact Howe: map Domain fst apply
-- statement:
--   The Compact Howe construction uses the map Domain fst apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MatrixFamilyBilateralSubstitutionScalarMonomial.lean#L24-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MatrixFamilyBilateralSubstitutionScalarMonomial.lean#L24-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TotalDegreeSubstFLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MatrixFamilyBilateralSubstitutionScalarMonomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open GlobalTheory GlobalTheory.CompactHowe

theorem GlobalTheory.CompactHowe.mapDomain_fst_apply {ι : Type} [DecidableEq ι] {N n : ℕ} (k : ι × Fin N × Fin n →₀ ℕ) (τ₀ : ι) :
    Finsupp.mapDomain Prod.fst k τ₀ = ∑ p ∈ k.support, if p.1 = τ₀ then k p else 0 := by sorry
