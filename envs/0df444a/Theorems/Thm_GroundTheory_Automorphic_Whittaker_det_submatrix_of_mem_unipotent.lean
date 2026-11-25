-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_det_submatrix_of_mem_unipotent
-- name    : GroundTheory.Automorphic.Whittaker.det_submatrix_of_mem_unipotent
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:40:55.073599+00:00
-- url     : https://prove2.me/theorems/d9b1bb67-612b-4c19-aa23-d098087c8c93
-- title:
--   Whittaker: det submatrix of mem unipotent
-- statement:
--   The Whittaker construction uses the det submatrix of mem unipotent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L449-L463
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L449-L463

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Matrix DoubleCoset
variable {F : Type*} [Field F] {n : ℕ}

theorem GroundTheory.Automorphic.Whittaker.det_submatrix_of_mem_unipotent {v : GL (Fin n) F} (hv : v ∈ Iwasawa.unipotent F n)
    {m : ℕ} {c : Fin m → Fin n} (hc : Function.Injective c) :
    ((v : Matrix (Fin n) (Fin n) F).submatrix c c).det = 1 := by sorry
