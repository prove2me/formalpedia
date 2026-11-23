-- Prove2me | Theorems.Thm_GlobalTheory_NormCompat_NormCont_exp_neg_one_pow
-- name    : GlobalTheory.NormCompat.NormCont.exp_neg_one_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:18:23.878029+00:00
-- url     : https://prove2.me/theorems/a8b4f3d2-475f-45fc-ae9d-b0272bbf606b
-- title:
--   Norm Cont: exp neg one pow
-- statement:
--   The Norm Cont construction uses the exp neg one pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NormCloseToOneOfCloseAbovePlace.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NormCloseToOneOfCloseAbovePlace.lean#L18-L19

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocUnitApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NormCloseToOneOfCloseAbovePlace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.NormCompat GlobalTheory.NormCompat.NormCont

theorem GlobalTheory.NormCompat.NormCont.exp_neg_one_pow (k : ℕ) : (WithZero.exp (-1 : ℤ)) ^ k = WithZero.exp (-(k : ℤ)) := by sorry
