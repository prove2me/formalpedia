-- Prove2me | Theorems.Thm_GlobalTheory_IwahoriFactor_flip_triple
-- name    : GlobalTheory.IwahoriFactor.flip_triple
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:23:56.668369+00:00
-- url     : https://prove2.me/theorems/51c7f709-2d5a-4dba-a92a-6043c6d98e13
-- title:
--   Iwahori Factor: flip triple
-- statement:
--   The Iwahori Factor construction uses the flip triple property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DvdInvOfBlockTriangular.lean#L188-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DvdInvOfBlockTriangular.lean#L188-L194

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

theorem GlobalTheory.IwahoriFactor.flip_triple (u l : Matrix (Fin n) (Fin n) O) (d : Fin n → O) :
    flip (u * Matrix.diagonal d * l) =
      flip u * Matrix.diagonal (fun i => d i.rev) * flip l := by sorry
