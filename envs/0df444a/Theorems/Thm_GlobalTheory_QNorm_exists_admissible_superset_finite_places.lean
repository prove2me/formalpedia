-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_exists_admissible_superset_finite_places
-- name    : GlobalTheory.QNorm.exists_admissible_superset_finite_places
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:23:34.509535+00:00
-- url     : https://prove2.me/theorems/6725db66-75f3-479b-9120-fc0244899c82
-- title:
--   QNorm: exists admissible superset finite places
-- statement:
--   The QNorm construction uses the exists admissible superset finite places property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsAdmissibleSupersetFinitePlaces.lean#L29-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsAdmissibleSupersetFinitePlaces.lean#L29-L87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsAdmissibleSupersetFinitePlaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm

theorem GlobalTheory.QNorm.exists_admissible_superset_finite_places : ∀ (F : Type) [Field F] [NumberField F]
    (S₀ : Finset (HeightOneSpectrum (𝓞 F))), ∃ S, S₀ ⊆ S ∧ admitted F S := by sorry
