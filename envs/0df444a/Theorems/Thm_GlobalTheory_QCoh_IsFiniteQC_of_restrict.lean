-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_IsFiniteQC_of_restrict
-- name    : GlobalTheory.QCoh.IsFiniteQC.of_restrict
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:06:47.665617+00:00
-- url     : https://prove2.me/theorems/bb4c526d-60e5-4bc5-8d89-36f04455cd5d
-- title:
--   Is Finite QC: of restrict
-- statement:
--   The Is Finite QC construction uses the of restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L280-L288
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L280-L288

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsLocalizedModuleGermLinearPointOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_TopologicalKrullDimLeOfIrreducibleCloseds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite TensorProduct IsLocalRing
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} {F G H : X.Modules} {U V : X.Opens}
attribute [instance 100] IsFiniteQC.isQuasicoherent
variable {Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g]

theorem GlobalTheory.QCoh.IsFiniteQC.of_restrict {ι : Type*} {Y : ι → Scheme.{u}} (g : ∀ i, Y i ⟶ X)
    [∀ i, IsOpenImmersion (g i)] (hcov : ∀ x : X, ∃ i, x ∈ (g i).opensRange)
    (h : ∀ i, IsFiniteQC (F.restrict (g i))) : IsFiniteQC F := by sorry
