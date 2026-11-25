-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_exact_map_pullback
-- name    : GlobalTheory.QCoh.exact_map_pullback
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:52:51.079543+00:00
-- url     : https://prove2.me/theorems/aa7e4c56-ea6b-422b-b678-b39314c09267
-- title:
--   QCoh: exact map pullback
-- statement:
--   The QCoh construction uses the exact map pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RestrictPullbackIsoHomAppPullbackSections.lean#L580-L583
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RestrictPullbackIsoHomAppPullbackSections.lean#L580-L583

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

theorem GlobalTheory.QCoh.exact_map_pullback {S : ShortComplex Y.Modules} (hS : S.Exact) [Epi S.g] :
    (S.map (Scheme.Modules.pullback f)).Exact ∧ Epi (S.map (Scheme.Modules.pullback f)).g := by sorry
