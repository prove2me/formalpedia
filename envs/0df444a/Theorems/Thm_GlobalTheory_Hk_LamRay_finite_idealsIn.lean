-- Prove2me | Theorems.Thm_GlobalTheory_Hk_LamRay_finite_idealsIn
-- name    : GlobalTheory.Hk.LamRay.finite_idealsIn
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T14:22:06.902117+00:00
-- url     : https://prove2.me/theorems/9748cdea-f6cf-43c0-8ae6-b9a872ac746d
-- title:
--   Lam Ray: finite ideals In
-- statement:
--   The Lam Ray construction uses the finite ideals In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SumLamIdealLe.lean#L132-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SumLamIdealLe.lean#L132-L133

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsImagQuadIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PrimeIdealsCountingBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumLamIdealLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.LamRay
variable {K : Type} [Field K] [NumberField K]

theorem GlobalTheory.Hk.LamRay.finite_idealsIn {M : ℕ} (D : RayData K M) (g : D.G) (n : ℕ) : (idealsIn D g n).Finite := by sorry
