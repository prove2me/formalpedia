-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_TorusE_val_mk
-- name    : GroundTheory.Automorphic.TorusE.val_mk
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:59:07.742041+00:00
-- url     : https://prove2.me/theorems/a772371a-f1f9-440f-9835-88e9cbf049b4
-- title:
--   Torus E: val mk
-- statement:
--   The Torus E construction uses the val mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjTorus.lean#L230-L230
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjTorus.lean#L230-L230

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianOrthogonal
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjCyclic
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjTorus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Module
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V : Type*} [AddCommGroup V] [Module E V]
variable [FiniteDimensional E V]
open GroundTheory.Automorphic.TorusE
variable {γ : V ≃ₗ[E] V}
omit [FiniteDimensional E V]

theorem GroundTheory.Automorphic.TorusE.val_mk (t : V ≃ₗ[E] V) (ht : t ∈ torusE γ) : (mk t ht).val = t := by sorry

attribute [defeq] GroundTheory.Automorphic.TorusE.val_mk
