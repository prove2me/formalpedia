-- Prove2me | Theorems.Thm_GlobalTheory_JR_DualScaledIntegers_exists_open_compact_annihilator
-- name    : GlobalTheory.JR.DualScaledIntegers.exists_open_compact_annihilator
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:26:59.373375+00:00
-- url     : https://prove2.me/theorems/2433ab99-02c0-44a0-a3fa-1f552426e826
-- title:
--   Dual Scaled Integers: exists open compact annihilator
-- statement:
--   The Dual Scaled Integers construction uses the exists open compact annihilator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsOpenCompactAnnihilatorScaledIntegersK.lean#L9-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsOpenCompactAnnihilatorScaledIntegersK.lean#L9-L64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSmallDualLattices
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsOpenCompactAnnihilatorScaledIntegersK
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.DualScaledIntegers

theorem GlobalTheory.JR.DualScaledIntegers.exists_open_compact_annihilator : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ c : F, c ≠ 0 → ∃ D : AddSubgroup A.K, (D : Set A.K) = {b : A.K | ∀ z : A.K, c • z ∈ A.OK → A.psiK ψ (z * b) = 1} ∧ IsOpen (D : Set A.K) ∧ IsCompact (D : Set A.K) := by sorry
