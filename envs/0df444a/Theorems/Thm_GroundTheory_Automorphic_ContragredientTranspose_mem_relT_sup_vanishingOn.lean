-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_mem_relT_sup_vanishingOn
-- name    : GroundTheory.Automorphic.ContragredientTranspose.mem_relT_sup_vanishingOn
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:48:04.489108+00:00
-- url     : https://prove2.me/theorems/61b10b27-9b6b-4488-ac66-a3689139a9c7
-- title:
--   Contragredient Transpose: mem rel T sup vanishing On
-- statement:
--   The Contragredient Transpose construction uses the mem rel T sup vanishing On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/GelfandKazhdan.lean#L484-L616
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/GelfandKazhdan.lean#L484-L616

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

theorem GroundTheory.Automorphic.ContragredientTranspose.mem_relT_sup_vanishingOn {Z : Set (GL (Fin n) F)} (hZ : IsClosed Z)
    (hZinv : ∀ h : ConjAct (GL (Fin n) F), ∀ x ∈ Z, h • x ∈ Z)
    (hZτ : ∀ x, transposeGL x ∈ Z ↔ x ∈ Z) {s : Set (GL (Fin n) F)} (hs : s.Countable)
    (hcov : Z ⊆ ⋃ x ∈ s, orbit (ConjAct (GL (Fin n) F)) x) {g : GL (Fin n) F → ℂ}
    (hg : g ∈ supportedIn (univ : Set (GL (Fin n) F))) :
    g ∈ relT (univ : Set (GL (Fin n) F)) ⊔ (supportedIn univ ⊓ vanishingOn Z) := by sorry
