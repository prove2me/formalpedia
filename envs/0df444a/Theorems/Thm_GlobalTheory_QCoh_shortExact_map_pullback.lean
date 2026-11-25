-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_shortExact_map_pullback
-- name    : GlobalTheory.QCoh.shortExact_map_pullback
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:02:15.524056+00:00
-- url     : https://prove2.me/theorems/6d071b69-0735-55e2-9dcb-cd1e8d4fb10f
-- title:
--   QCoh: short Exact map pullback
-- statement:
--   The QCoh construction uses the short Exact map pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RestrictPullbackIsoHomAppPullbackSections.lean#L615-L621
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RestrictPullbackIsoHomAppPullbackSections.lean#L615-L621

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

theorem GlobalTheory.QCoh.shortExact_map_pullback [Flat f] {S : ShortComplex Y.Modules}
    (hS : S.ShortExact) [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] :
    (S.map (Scheme.Modules.pullback f)).ShortExact := by sorry
