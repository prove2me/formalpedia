-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_supportedIn_le_relT_sup
-- name    : GroundTheory.Automorphic.ContragredientTranspose.supportedIn_le_relT_sup
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T02:56:21.060416+00:00
-- url     : https://prove2.me/theorems/4fc486cb-53ab-5e09-b9ee-e2e59c328356
-- title:
--   Contragredient Transpose: supported In le rel T sup
-- statement:
--   The Contragredient Transpose construction uses the supported In le rel T sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/GelfandKazhdan.lean#L225-L359
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/GelfandKazhdan.lean#L225-L359

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerDistribution
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_MatrixSimilarity
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_GelfandKazhdan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.ContragredientTranspose
open Set Filter Topology MulAction Matrix GroundTheory.Automorphic.Whittaker
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

theorem GroundTheory.Automorphic.ContragredientTranspose.supportedIn_le_relT_sup {U C : Set (GL (Fin n) F)} (hU : IsOpen U) (hC : IsClosed C)
    {x₀ : GL (Fin n) F} (hO : U ∩ C = orbit (ConjAct (GL (Fin n) F)) x₀)
    (hUinv : ∀ h : ConjAct (GL (Fin n) F), ∀ x ∈ U, h • x ∈ U)
    (hUτ : ∀ x, transposeGL x ∈ U ↔ x ∈ U) {S : GL (Fin n) F} (hS : transposeGL S = S)
    (hSx : S * x₀ * S⁻¹ = transposeGL x₀) :
    supportedIn U ≤ relT U ⊔ (supportedIn U ⊓ vanishingOn C) := by sorry
