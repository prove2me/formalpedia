-- Prove2me | Theorems.Thm_GlobalTheory_AdicNoeth_isNoetherianRing_graded
-- name    : GlobalTheory.AdicNoeth.isNoetherianRing_graded
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:55:34.390911+00:00
-- url     : https://prove2.me/theorems/d6bb3ce5-5f3e-4a96-b0cc-fde7f6878fbe
-- title:
--   Adic Noeth: is Noetherian Ring graded
-- statement:
--   The Adic Noeth construction uses the is Noetherian Ring graded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsNoetherianRingOfIsAdicComplete.lean#L8-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsNoetherianRingOfIsAdicComplete.lean#L8-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGradedRingKernelLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsNoetherianRingOfIsAdicComplete
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.AdicNoeth

theorem GlobalTheory.AdicNoeth.isNoetherianRing_graded {R : Type} [CommRing R] (I : Ideal R) (hI : I.FG)
    [IsNoetherianRing (R ⧸ I)] : IsNoetherianRing (reesAlgebra I ⧸ reesShiftIdeal I) := by sorry
