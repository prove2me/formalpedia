-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_isUnit_det_of_unitary
-- name    : GroundTheory.Automorphic.isUnit_det_of_unitary
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:55:12.148944+00:00
-- url     : https://prove2.me/theorems/af0c67e2-77f4-4ea5-9790-1c004bbd091c
-- title:
--   Automorphic: is Unit det of unitary
-- statement:
--   The Automorphic construction uses the is Unit det of unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianSpaces.lean#L37-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianSpaces.lean#L37-L45

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_QuadraticConj
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianSpaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Module Matrix
variable {A : Type*} [CommRing A] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem GroundTheory.Automorphic.isUnit_det_of_unitary (s : A →+* A) {H : Matrix ι ι A} (hH : IsUnit H.det)
    {M : Matrix ι ι A} (hM : (M.map s)ᵀ * H * M = H) : IsUnit M.det := by sorry
