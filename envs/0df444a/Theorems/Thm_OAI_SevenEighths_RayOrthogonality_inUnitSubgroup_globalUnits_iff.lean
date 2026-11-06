-- Prove2me | Theorems.Thm_OAI_SevenEighths_RayOrthogonality_inUnitSubgroup_globalUnits_iff
-- name    : OAI.SevenEighths.RayOrthogonality.inUnitSubgroup_globalUnits_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:00:03.300085+00:00
-- url     : https://prove2.me/theorems/7b74a255-d813-43d4-a3e2-2f6f489e075d
-- title:
--   Ray Orthogonality: in Unit Subgroup global Units iff
-- statement:
--   The Ray Orthogonality construction uses the in Unit Subgroup global Units iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/RayOrthogonality.lean#L111-L117
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/RayOrthogonality.lean#L111-L117

import Definitions.Def_OAI_NumberTheory_DirichletL_IdealCharacter
import Mathlib.NumberTheory.MulChar.Duality
import Definitions.Def_OAI_NumberTheory_DirichletL_RayOrthogonality
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.RayOrthogonality
open scoped Classical
noncomputable section
variable {A : Type*} [CommRing A] (M : Ideal A) [Finite (A ⧸ M)]
omit [Finite (A ⧸ M)]

theorem OAI.SevenEighths.RayOrthogonality.inUnitSubgroup_globalUnits_iff (r : A ⧸ M) :
    inUnitSubgroup (globalUnits M) r ↔ principalResidue M r := by sorry
