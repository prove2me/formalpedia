-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HermitianForm_mem_unitaryGroup
-- name    : GroundTheory.Automorphic.HermitianForm.mem_unitaryGroup
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:32:07.686169+00:00
-- url     : https://prove2.me/theorems/401db249-a53a-4696-914d-5ba1f2824aaa
-- title:
--   Hermitian Form: mem unitary Group
-- statement:
--   The Hermitian Form construction uses the mem unitary Group property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianSpaces.lean#L89-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianSpaces.lean#L89-L90

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
open GroundTheory.Automorphic.HermitianForm

theorem GroundTheory.Automorphic.HermitianForm.mem_unitaryGroup {h : HermitianForm F E V} {g : V ≃ₗ[E] V} :
    g ∈ h.unitaryGroup ↔ ∀ x y, h.toSesq (g x) (g y) = h.toSesq x y := by sorry
