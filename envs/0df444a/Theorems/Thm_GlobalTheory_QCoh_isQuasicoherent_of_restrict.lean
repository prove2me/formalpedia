-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_isQuasicoherent_of_restrict
-- name    : GlobalTheory.QCoh.isQuasicoherent_of_restrict
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:33.83562+00:00
-- url     : https://prove2.me/theorems/4e8e655e-3513-4949-98a8-a1acce4aeac2
-- title:
--   QCoh: is Quasicoherent of restrict
-- statement:
--   The QCoh construction uses the is Quasicoherent of restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L257-L277
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L257-L277

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite TensorProduct
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} (F : X.Modules) {U V W : X.Opens}
set_option backward.isDefEq.respectTransparency false

theorem GlobalTheory.QCoh.isQuasicoherent_of_restrict {ι : Type*} {Y : ι → Scheme.{u}} (g : ∀ i, Y i ⟶ X)
    [∀ i, IsOpenImmersion (g i)] (hcov : ∀ x : X, ∃ i, x ∈ (g i).opensRange)
    (h : ∀ i, (F.restrict (g i)).IsQuasicoherent) : F.IsQuasicoherent := by sorry
