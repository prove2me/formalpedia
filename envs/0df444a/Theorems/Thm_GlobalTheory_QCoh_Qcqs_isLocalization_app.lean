-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_Qcqs_isLocalization_app
-- name    : GlobalTheory.QCoh.Qcqs.isLocalization_app
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T09:31:16.118799+00:00
-- url     : https://prove2.me/theorems/cf09a3f6-eafe-4d66-afc4-6fe8f572de52
-- title:
--   Qcqs: is Localization app
-- statement:
--   The Qcqs construction uses the is Localization app property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsAffineHomOfIsPullbackSpecMap.lean#L95-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsAffineHomOfIsPullbackSpecMap.lean#L95-L118

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsAffineHomOfIsPullbackSpecMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh GlobalTheory.QCoh.Qcqs
variable {R L : CommRingCat.{u}} [Algebra R L] (S : Submonoid R) [IsLocalization S L]
  {X Y : Scheme.{u}} {p : X ⟶ Spec R} {q : Y ⟶ Spec L} {g : Y ⟶ X}
  (H : IsPullback g q p (Spec.map (CommRingCat.ofHom (algebraMap R L))))
include H

theorem GlobalTheory.QCoh.Qcqs.isLocalization_app {V : X.Opens} (hV : IsAffineOpen V) :
    letI := (g.app V).hom.toAlgebra
    IsLocalization (S.map (baseRingHom p V).hom) Γ(Y, g ⁻¹ᵁ V) := by sorry
