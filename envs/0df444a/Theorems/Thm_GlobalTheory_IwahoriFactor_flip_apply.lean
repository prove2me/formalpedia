-- Prove2me | Theorems.Thm_GlobalTheory_IwahoriFactor_flip_apply
-- name    : GlobalTheory.IwahoriFactor.flip_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:26:41.782065+00:00
-- url     : https://prove2.me/theorems/df8cb61e-8103-49e8-bacd-f06ea0ea2c2d
-- title:
--   Iwahori Factor: flip apply
-- statement:
--   The Iwahori Factor construction uses the flip apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DvdInvOfBlockTriangular.lean#L182-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DvdInvOfBlockTriangular.lean#L182-L183

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UdlApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IwahoriFactorisation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DvdInvOfBlockTriangular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.IwahoriFactor
variable {O : Type} [CommRing O] {n : ℕ}

theorem GlobalTheory.IwahoriFactor.flip_apply (g : Matrix (Fin n) (Fin n) O) (i j : Fin n) :
    flip g i j = g i.rev j.rev := by sorry
