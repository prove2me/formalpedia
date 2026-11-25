-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_shortExact_map_pushforward
-- name    : GlobalTheory.QCoh.shortExact_map_pushforward
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:03:39.225181+00:00
-- url     : https://prove2.me/theorems/89ea9172-65ba-49b2-a6dc-5b24c7e27ee1
-- title:
--   QCoh: short Exact map pushforward
-- statement:
--   The QCoh construction uses the short Exact map pushforward property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RestrictPullbackIsoHomAppPullbackSections.lean#L571-L578
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RestrictPullbackIsoHomAppPullbackSections.lean#L571-L578

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

theorem GlobalTheory.QCoh.shortExact_map_pushforward [IsAffineHom f] {S : ShortComplex X.Modules}
    (hS : S.ShortExact) [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent] :
    (S.map (Scheme.Modules.pushforward f)).ShortExact := by sorry
