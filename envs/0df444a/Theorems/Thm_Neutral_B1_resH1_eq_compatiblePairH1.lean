-- Prove2me | Theorems.Thm_Neutral_B1_resH1_eq_compatiblePairH1
-- name    : Neutral.B1.resH1_eq_compatiblePairH1
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:05:25.413229+00:00
-- url     : https://prove2.me/theorems/14792502-e809-4313-9e89-38b80501e2c4
-- title:
--   B1: res H1 eq compatible Pair H1
-- statement:
--   The B1 construction uses the res H1 eq compatible Pair H1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/Duality.lean#L274-L278
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/Duality.lean#L274-L278

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

theorem Neutral.B1.resH1_eq_compatiblePairH1 {H : Type*} [Group H] [TopologicalSpace H] (phi : H →* G)
    (hphi : Continuous phi) :
    resH1 rho phi hphi =
      pairH1DecompositionMap rho (rho.comp phi) phi hphi LinearMap.id continuous_id (fun _ _ => rfl) := by sorry
