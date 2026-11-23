-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_baseTrace_tmul
-- name    : GroundTheory.Automorphic.baseTrace_tmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:31:40.01471+00:00
-- url     : https://prove2.me/theorems/5283dc53-989b-4330-85ab-8733de37ba95
-- title:
--   Automorphic: base Trace tmul
-- statement:
--   The Automorphic construction uses the base Trace tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DefiniteClassNumber/HermTraceSelfOfHermValue.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DefiniteClassNumber/HermTraceSelfOfHermValue.lean#L23-L25

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Anisotropic
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_HermTraceSelfOfHermValue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Module Matrix TensorProduct
variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] (H : Matrix ι ι E)
variable (K E) (R : Type*) [CommRing R] [Algebra K R]
variable {K E R}
omit [Algebra.IsQuadraticExtension K E]

theorem GroundTheory.Automorphic.baseTrace_tmul (r : R) (e : E) :
    baseTrace K E R (r ⊗ₜ e) = algebraMap K R (Algebra.trace K E e) * r := by sorry
