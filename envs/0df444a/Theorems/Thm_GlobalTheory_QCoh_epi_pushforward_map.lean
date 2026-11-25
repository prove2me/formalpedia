-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_epi_pushforward_map
-- name    : GlobalTheory.QCoh.epi_pushforward_map
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:02:04.238305+00:00
-- url     : https://prove2.me/theorems/92387cd2-5384-532d-98d3-aa4e67c35bc2
-- title:
--   QCoh: epi pushforward map
-- statement:
--   The QCoh construction uses the epi pushforward map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RestrictPullbackIsoHomAppPullbackSections.lean#L565-L569
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RestrictPullbackIsoHomAppPullbackSections.lean#L565-L569

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

theorem GlobalTheory.QCoh.epi_pushforward_map [IsAffineHom f] (φ : F ⟶ F') [Epi φ] [F.IsQuasicoherent]
    [F'.IsQuasicoherent] : Epi ((Scheme.Modules.pushforward f).map φ) := by sorry
