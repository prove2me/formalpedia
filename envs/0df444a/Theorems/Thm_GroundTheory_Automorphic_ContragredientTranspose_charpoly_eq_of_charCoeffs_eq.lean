-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_charpoly_eq_of_charCoeffs_eq
-- name    : GroundTheory.Automorphic.ContragredientTranspose.charpoly_eq_of_charCoeffs_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:47:27.686876+00:00
-- url     : https://prove2.me/theorems/ed604877-ccfe-465f-a089-9481a0c0ebae
-- title:
--   Contragredient Transpose: charpoly eq of char Coeffs eq
-- statement:
--   The Contragredient Transpose construction uses the charpoly eq of char Coeffs eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/GelfandKazhdan.lean#L644-L651
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/GelfandKazhdan.lean#L644-L651

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
omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem GroundTheory.Automorphic.ContragredientTranspose.charpoly_eq_of_charCoeffs_eq {x y : GL (Fin n) F} (h : charCoeffs x = charCoeffs y) :
    (x : Matrix (Fin n) (Fin n) F).charpoly = (y : Matrix (Fin n) (Fin n) F).charpoly := by sorry
