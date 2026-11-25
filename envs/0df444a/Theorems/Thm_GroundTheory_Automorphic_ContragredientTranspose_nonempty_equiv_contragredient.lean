-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_nonempty_equiv_contragredient
-- name    : GroundTheory.Automorphic.ContragredientTranspose.nonempty_equiv_contragredient
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:18:57.104915+00:00
-- url     : https://prove2.me/theorems/1802b7df-f8e5-42d3-874f-b0366760370f
-- title:
--   Contragredient Transpose: nonempty equiv contragredient
-- statement:
--   The Contragredient Transpose construction uses the nonempty equiv contragredient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose.lean#L35-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose.lean#L35-L55

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_GelfandKazhdan
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_Character
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLocal
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_MapThetaTInvariant
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.ContragredientTranspose
open MeasureTheory Measure GroundTheory.Automorphic.Whittaker
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

theorem GroundTheory.Automorphic.ContragredientTranspose.nonempty_equiv_contragredient {V : Type*} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) F) V) (hπ : IsAdmissible π) [π.IsIrreducible] :
    Nonempty ((contragredient π).Equiv
      (π.comp (thetaT : GL (Fin n) F ≃* GL (Fin n) F).toMonoidHom)) := by sorry
