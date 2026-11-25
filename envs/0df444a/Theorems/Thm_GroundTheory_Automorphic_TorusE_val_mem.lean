-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_TorusE_val_mem
-- name    : GroundTheory.Automorphic.TorusE.val_mem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:59:17.971804+00:00
-- url     : https://prove2.me/theorems/bcdc600b-0053-4649-a0ac-52fce91f3a49
-- title:
--   Torus E: val mem
-- statement:
--   The Torus E construction uses the val mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjTorus.lean#L225-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjTorus.lean#L225-L225

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

theorem GroundTheory.Automorphic.TorusE.val_mem (t : TorusE γ) : t.val ∈ torusE γ := by sorry
