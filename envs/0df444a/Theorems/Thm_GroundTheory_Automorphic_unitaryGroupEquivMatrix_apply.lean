-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_unitaryGroupEquivMatrix_apply
-- name    : GroundTheory.Automorphic.unitaryGroupEquivMatrix_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:32:07.621812+00:00
-- url     : https://prove2.me/theorems/d75c0fbc-4ff2-4a79-bf56-86af3d3cfc62
-- title:
--   Automorphic: unitary Group Equiv Matrix apply
-- statement:
--   The Automorphic construction uses the unitary Group Equiv Matrix apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianSpaces.lean#L188-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianSpaces.lean#L188-L192

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
variable (F E : Type*) [Field F] [CommRing E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable (V : Type*) [AddCommGroup V] [Module E V]
variable {F E V}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem GroundTheory.Automorphic.unitaryGroupEquivMatrix_apply (h : HermitianForm F E V) (v : Basis ι E V)
    (g : h.unitaryGroup) :
    ((unitaryGroupEquivMatrix h v g : GL ι E) : Matrix ι ι E) =
      LinearMap.toMatrix v v ((g : V ≃ₗ[E] V) : V →ₗ[E] V) := by sorry
