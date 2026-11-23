-- Prove2me | Theorems.Thm_GlobalTheory_Pat_PhiFin_of_surjective
-- name    : GlobalTheory.Pat.PhiFin.of_surjective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:54:34.072342+00:00
-- url     : https://prove2.me/theorems/7fdceb72-cfe3-4fdf-b1c6-993446ee9b5e
-- title:
--   Phi Fin: of surjective
-- statement:
--   The Phi Fin construction uses the of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/FiniteCocycles.lean#L174-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/FiniteCocycles.lean#L174-L187

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FiniteCocycles
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Polynomial IsLocalRing
noncomputable section
open IsLocalRing
open GlobalTheory GlobalTheory.Pat

theorem GlobalTheory.Pat.PhiFin.of_surjective {l : ℕ} {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']
    (h : PhiFin l G) (p : G →* G') (hc : Continuous p) (hs : Function.Surjective p) : PhiFin l G' := by sorry
