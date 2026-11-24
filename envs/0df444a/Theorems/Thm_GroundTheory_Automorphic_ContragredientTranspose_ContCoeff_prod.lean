-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_ContCoeff_prod
-- name    : GroundTheory.Automorphic.ContragredientTranspose.ContCoeff.prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:09:36.916525+00:00
-- url     : https://prove2.me/theorems/f82e7409-e900-48d2-a223-d871e62b06cf
-- title:
--   Cont Coeff: prod
-- statement:
--   The Cont Coeff construction uses the prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/MatrixSimilarity.lean#L171-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/MatrixSimilarity.lean#L171-L179

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_MatrixSimilarity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.ContragredientTranspose
open Polynomial
variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
variable {α : Type*} [TopologicalSpace α]

theorem GroundTheory.Automorphic.ContragredientTranspose.ContCoeff.prod {ι : Type*} (s : Finset ι) {P : ι → α → F[X]}
    (hP : ∀ i ∈ s, ContCoeff (P i)) : ContCoeff fun a => ∏ i ∈ s, P i a := by sorry
