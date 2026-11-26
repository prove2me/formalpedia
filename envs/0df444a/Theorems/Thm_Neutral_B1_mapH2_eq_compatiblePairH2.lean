-- Prove2me | Theorems.Thm_Neutral_B1_mapH2_eq_compatiblePairH2
-- name    : Neutral.B1.mapH2_eq_compatiblePairH2
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:03:47.354663+00:00
-- url     : https://prove2.me/theorems/b0b2bdef-34ed-58d2-90f4-20cb2f60ac2a
-- title:
--   B1: map H2 eq compatible Pair H2
-- statement:
--   The B1 construction uses the map H2 eq compatible Pair H2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/Duality.lean#L298-L301
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/Duality.lean#L298-L301

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Duality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation
open Neutral Neutral.B1
set_option linter.unusedVariables false
noncomputable section
open Representation
variable {R : Type*} [CommRing R]
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
variable (rho : Representation R G M)
variable {M' : Type*} [AddCommGroup M'] [Module R M'] [TopologicalSpace M']
  [IsTopologicalAddGroup M'] [ContinuousConstSMul R M']
  (rho' : Representation R G M') (u : M →ₗ[R] M') (hu : Continuous u)
  (hequiv : ∀ g m, u (rho g m) = rho' g (u m))

theorem Neutral.B1.mapH2_eq_compatiblePairH2 :
    mapH2 rho rho' u hu hequiv =
      compatiblePairH2 rho rho' (MonoidHom.id G) continuous_id u hu hequiv := by sorry
