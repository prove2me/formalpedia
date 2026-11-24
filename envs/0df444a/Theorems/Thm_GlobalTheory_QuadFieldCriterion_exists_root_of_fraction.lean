-- Prove2me | Theorems.Thm_GlobalTheory_QuadFieldCriterion_exists_root_of_fraction
-- name    : GlobalTheory.QuadFieldCriterion.exists_root_of_fraction
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:10:01.116137+00:00
-- url     : https://prove2.me/theorems/cd2c6757-96ea-41e7-9db5-af30839c2dcf
-- title:
--   Quad Field Criterion: exists root of fraction
-- statement:
--   The Quad Field Criterion construction uses the exists root of fraction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IsFieldIffNoResidualRoot.lean#L32-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IsFieldIffNoResidualRoot.lean#L32-L40

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

theorem GlobalTheory.QuadFieldCriterion.exists_root_of_fraction {O K : Type*} [CommRing O] [IsDomain O] [IsIntegrallyClosed O]
    [Field K] [Algebra O K] [IsFractionRing O K] (t n : O) (x : K)
    (hx : x ^ 2 - algebraMap O K t * x + algebraMap O K n = 0) :
    ∃ s : O, s ^ 2 - t * s + n = 0 := by sorry
