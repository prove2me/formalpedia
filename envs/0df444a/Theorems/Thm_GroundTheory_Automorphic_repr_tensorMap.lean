-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_repr_tensorMap
-- name    : GroundTheory.Automorphic.repr_tensorMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:33.671565+00:00
-- url     : https://prove2.me/theorems/5fda59b2-17b8-47ba-b44b-dc3f86d0bcf3
-- title:
--   Automorphic: repr tensor Map
-- statement:
--   The Automorphic construction uses the repr tensor Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryGroupEquations.lean#L42-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryGroupEquations.lean#L42-L49

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryGroupScheme
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryGroupEquations
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Module Matrix TensorProduct
variable {F E : Type*} [Field F] [CommRing E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] (b : Basis κ F E)
variable (R : Type*) [CommRing R] [Algebra F R] {S : Type*} [CommRing S] [Algebra F S]
variable {R}
omit [Algebra.IsQuadraticExtension F E] [Fintype κ]

theorem GroundTheory.Automorphic.repr_tensorMap (f : R →ₐ[F] S) (z : R ⊗[F] E) (k : κ) :
    (Algebra.TensorProduct.basis S b).repr (tensorMap E f z) k =
      f ((Algebra.TensorProduct.basis R b).repr z k) := by sorry
