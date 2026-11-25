-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_TorusE_val_mul
-- name    : GroundTheory.Automorphic.TorusE.val_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:59:06.825211+00:00
-- url     : https://prove2.me/theorems/125568d5-7d70-47db-9fbe-84925af4dfe0
-- title:
--   Torus E: val mul
-- statement:
--   The Torus E construction uses the val mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjTorus.lean#L238-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjTorus.lean#L238-L238

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
variable [Fact (IsRegularSemisimple γ)]

theorem GroundTheory.Automorphic.TorusE.val_mul (a b : TorusE γ) : (a * b).val = a.val * b.val := by sorry

attribute [defeq] GroundTheory.Automorphic.TorusE.val_mul
