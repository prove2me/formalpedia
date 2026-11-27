-- Prove2me | Theorems.Thm_GlobalTheory_exists_complete_dvr_finite_residueField
-- name    : GlobalTheory.exists_complete_dvr_finite_residueField
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:44:26.832809+00:00
-- url     : https://prove2.me/theorems/c69db959-8197-5a28-9713-14ff3c92f2e6
-- title:
--   Global Theory: exists complete dvr finite residue Field
-- statement:
--   The Global Theory construction uses the exists complete dvr finite residue Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ResidueFieldMapAdicCompletionSurjective.lean#L58-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ResidueFieldMapAdicCompletionSurjective.lean#L58-L74

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ResidueFieldMapAdicCompletionSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory

theorem GlobalTheory.exists_complete_dvr_finite_residueField : ∀ (D : Type) [CommRing D] [IsDomain D] [IsLocalRing D], IsNoetherianRing D → ringKrullDim D = 1 → Finite (ResidueField D) → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : IsAdicComplete (maximalIdeal V) V) (g : D →+* V), Function.Injective g ∧ IsLocalHom g ∧ Finite (ResidueField V) := by sorry
