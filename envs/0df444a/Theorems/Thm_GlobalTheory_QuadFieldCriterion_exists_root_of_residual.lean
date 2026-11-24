-- Prove2me | Theorems.Thm_GlobalTheory_QuadFieldCriterion_exists_root_of_residual
-- name    : GlobalTheory.QuadFieldCriterion.exists_root_of_residual
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:09:55.059622+00:00
-- url     : https://prove2.me/theorems/b5e6cd9c-23a5-4f86-85d3-3d2aba6ca0a8
-- title:
--   Quad Field Criterion: exists root of residual
-- statement:
--   The Quad Field Criterion construction uses the exists root of residual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IsFieldIffNoResidualRoot.lean#L11-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IsFieldIffNoResidualRoot.lean#L11-L30

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_SelfDualUnramifiedPlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IsFieldIffNoResidualRoot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory GlobalTheory.QuadFieldCriterion
open Polynomial IsLocalRing

theorem GlobalTheory.QuadFieldCriterion.exists_root_of_residual {O : Type*} [CommRing O] [IsLocalRing O]
    [HenselianRing O (maximalIdeal O)] (t n : O) (hd : IsUnit (t ^ 2 - 4 * n))
    (r : ResidueField O) (hr : r ^ 2 - residue O t * r + residue O n = 0) :
    ∃ s : O, s ^ 2 - t * s + n = 0 := by sorry
