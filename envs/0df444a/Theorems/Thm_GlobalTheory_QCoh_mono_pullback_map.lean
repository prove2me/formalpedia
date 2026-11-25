-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_mono_pullback_map
-- name    : GlobalTheory.QCoh.mono_pullback_map
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:03:48.13433+00:00
-- url     : https://prove2.me/theorems/d421bfa4-4e53-4c46-8413-56de6dd4c15c
-- title:
--   QCoh: mono pullback map
-- statement:
--   The QCoh construction uses the mono pullback map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RestrictPullbackIsoHomAppPullbackSections.lean#L599-L613
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RestrictPullbackIsoHomAppPullbackSections.lean#L599-L613

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RestrictPullbackIsoHomAppPullbackSections
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite TensorProduct
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X Y : Scheme.{u}} {F F' : X.Modules}
variable (f : X ⟶ Y)

theorem GlobalTheory.QCoh.mono_pullback_map [Flat f] {G G' : Y.Modules} (φ : G ⟶ G') [Mono φ] [G.IsQuasicoherent]
    [G'.IsQuasicoherent] : Mono ((Scheme.Modules.pullback f).map φ) := by sorry
