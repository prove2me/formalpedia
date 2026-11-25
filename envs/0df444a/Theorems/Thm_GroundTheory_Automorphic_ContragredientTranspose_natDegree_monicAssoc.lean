-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_natDegree_monicAssoc
-- name    : GroundTheory.Automorphic.ContragredientTranspose.natDegree_monicAssoc
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:28:46.320803+00:00
-- url     : https://prove2.me/theorems/d70d0a7b-2940-4f96-9687-49beafb2440f
-- title:
--   Contragredient Transpose: nat Degree monic Assoc
-- statement:
--   The Contragredient Transpose construction uses the nat Degree monic Assoc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/MatrixSimilarity.lean#L29-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/MatrixSimilarity.lean#L29-L30

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
variable {F : Type*} [Field F]

theorem GroundTheory.Automorphic.ContragredientTranspose.natDegree_monicAssoc {q : F[X]} (hq : q ≠ 0) : (monicAssoc q).natDegree = q.natDegree := by sorry
