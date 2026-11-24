-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwo_BZeroGood_halfPlane_mem_nhds_zero
-- name    : GlobalTheory.HeckeTwo.BZeroGood.halfPlane_mem_nhds_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T14:06:32.986025+00:00
-- url     : https://prove2.me/theorems/56360bf1-fb11-41e9-8fef-2f92f40305ba
-- title:
--   BZero Good: half Plane mem nhds zero
-- statement:
--   The BZero Good construction uses the half Plane mem nhds zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeEisensteinZeroFrequencyPartIsSmoothHolomorphic.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeEisensteinZeroFrequencyPartIsSmoothHolomorphic.lean#L29-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSmoothHolomorphicInSigmaFamilyMulLeft
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierConstantAtZeroDifferentiableOnStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierConstantAtZeroZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UpperHalfPlaneProductProdImRpowContDiffOnStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdImIteratedWirtingerDerivWordDifferentiableOnStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeEisensteinZeroFrequencyPartIsSmoothHolomorphic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwo
open GlobalTheory.HeckeTwo.BZeroGood

theorem GlobalTheory.HeckeTwo.BZeroGood.halfPlane_mem_nhds_zero : halfPlane ∈ nhds (0 : ℂ) := by sorry
