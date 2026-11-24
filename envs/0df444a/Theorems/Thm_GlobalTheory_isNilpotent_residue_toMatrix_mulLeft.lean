-- Prove2me | Theorems.Thm_GlobalTheory_isNilpotent_residue_toMatrix_mulLeft
-- name    : GlobalTheory.isNilpotent_residue_toMatrix_mulLeft
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:58:13.915541+00:00
-- url     : https://prove2.me/theorems/21514ce6-f814-4bd1-8e9f-76ab8ce63325
-- title:
--   Global Theory: is Nilpotent residue to Matrix mul Left
-- statement:
--   The Global Theory construction uses the is Nilpotent residue to Matrix mul Left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsNilpotentResidueToMatrixMulLeft.lean#L6-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsNilpotentResidueToMatrixMulLeft.lean#L6-L55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsNilpotentResidueToMatrixMulLeft
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory

theorem GlobalTheory.isNilpotent_residue_toMatrix_mulLeft : ∀ (R S : Type) [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S] [Algebra R S] (n : ℕ) (b : Module.Basis (Fin n) R S) (t : S), t ∈ IsLocalRing.maximalIdeal S → IsNilpotent ((LinearMap.toMatrix b b (LinearMap.mulLeft R t)).map (IsLocalRing.residue R)) := by sorry
