-- Prove2me | Theorems.Thm_GlobalTheory_Hk_LamRay_lamRay_props
-- name    : GlobalTheory.Hk.LamRay.lamRay_props
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T14:21:49.692804+00:00
-- url     : https://prove2.me/theorems/6bee6a05-d91a-4fca-9dea-cf8320c36594
-- title:
--   Lam Ray: lam Ray props
-- statement:
--   The Lam Ray construction uses the lam Ray props property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SumLamIdealLe.lean#L135-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SumLamIdealLe.lean#L135-L170

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

theorem GlobalTheory.Hk.LamRay.lamRay_props : ∀ (K : Type) [Field K] [NumberField K] (d M : ℕ) (x : K), d.Prime → d % 4 = 3 → 100 ≤ d → x ^ 2 = -(d : K) → Module.finrank ℚ K = 2 → 3 ≤ M → ∀ D : RayData K M, (∀ g n, 0 ≤ lamRay D g n) ∧ (∀ n : ℕ, ∑ g : D.G, lamRay D g n ≤ 2 * Λ n) ∧ ∀ p : ℕ, p.Prime → lamRay D 1 p ≠ 0 → GlobalTheory.Mem.An.NormOne d M p := by sorry
