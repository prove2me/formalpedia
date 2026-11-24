-- Prove2me | Theorems.Thm_GlobalTheory_LatFin_finite_automorphisms
-- name    : GlobalTheory.LatFin.finite_automorphisms
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:03:55.059179+00:00
-- url     : https://prove2.me/theorems/1c111f2f-7314-415c-a275-4da241237540
-- title:
--   Lat Fin: finite automorphisms
-- statement:
--   The Lat Fin construction uses the finite automorphisms property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsIntMulIntegral.lean#L94-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsIntMulIntegral.lean#L94-L108

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsIntMulMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsIntMulIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.LatFin
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.LatFin.finite_automorphisms (r : ℕ) (X : Data E r) (R : ℝ) :
    {γ : GL (Fin r) E | IsUStab X.Gm X.Λ γ ∧ ∀ (τ : X.Ψ) (a b : Fin r),
      ‖τ.1 ((γ : Matrix (Fin r) (Fin r) E) a b)‖ ≤ R}.Finite := by sorry
