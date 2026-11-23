-- Prove2me | Theorems.Thm_GlobalTheory_PlaneTheta_abs_tsum_le
-- name    : GlobalTheory.PlaneTheta.abs_tsum_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:42:19.861385+00:00
-- url     : https://prove2.me/theorems/3a48e4d2-af06-46a8-bf3f-02b72b152954
-- title:
--   Plane Theta: abs tsum le
-- statement:
--   The Plane Theta construction uses the abs tsum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LatticeThetaAsymptotics.lean#L27-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LatticeThetaAsymptotics.lean#L27-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LatticeThetaAsymptotics
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Asymptotics
open scoped RealInnerProductSpace
open GlobalTheory GlobalTheory.PlaneTheta

theorem GlobalTheory.PlaneTheta.abs_tsum_le {ι : Type*} {q f : ι → ℝ} {δ s : ℝ} (hs : 1 ≤ s)
    (h : Summable fun i => Real.exp (-q i)) (hf : ∀ i, |f i| ≤ Real.exp (-(s * q i)))
    (hδ : ∀ i, f i ≠ 0 → δ ≤ q i) :
    |∑' i, f i| ≤ (Real.exp δ * ∑' i, Real.exp (-q i)) * Real.exp (-δ * s) := by sorry
