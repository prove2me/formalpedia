-- Prove2me | Theorems.Thm_GlobalTheory_PMonE_existsUnique_integral_gsum_eq
-- name    : GlobalTheory.PMonE.existsUnique_integral_gsum_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:33:22.522797+00:00
-- url     : https://prove2.me/theorems/394ea6f0-9548-4766-89a8-cdcfb1611151
-- title:
--   PMon E: exists Unique integral gsum eq
-- statement:
--   The PMon E construction uses the exists Unique integral gsum eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUniqueIntegralAdditiveSystemFrobeniusPower.lean#L45-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUniqueIntegralAdditiveSystemFrobeniusPower.lean#L45-L109

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUniqueIntegralAdditiveSystemFrobeniusPower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PMonE Finset
open GlobalTheory GlobalTheory.PMonE

theorem GlobalTheory.PMonE.existsUnique_integral_gsum_eq (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F]
    (p : ℕ) [Fact p.Prime] [CharP F p] (m : Type) [Fintype m] [DecidableEq m] (e D : ℕ) (_he : 0 < e)
    (U : ℕ → Matrix m m F) (h0 : ∀ i j, ‖(U 0 - 1) i j‖ < 1) (h1 : ∀ n, 1 ≤ n → ∀ i j, ‖U n i j‖ < 1)
    (b : m → F) (hb : Integral b) : ∃! y : m → F, Integral y ∧ gsum (p ^ e) D U y = b := by sorry
