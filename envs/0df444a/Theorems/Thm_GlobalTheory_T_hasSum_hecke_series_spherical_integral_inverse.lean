-- Prove2me | Theorems.Thm_GlobalTheory_T_hasSum_hecke_series_spherical_integral_inverse
-- name    : GlobalTheory.T.hasSum_hecke_series_spherical_integral_inverse
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:02:46.087969+00:00
-- url     : https://prove2.me/theorems/ec69faef-80d1-4ff3-a872-91f15f09dbe7
-- title:
--   T: has Sum hecke series spherical integral inverse
-- statement:
--   The T construction uses the has Sum hecke series spherical integral inverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/HasSumHeckeSeriesSphericalIntegralInverseStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/HasSumHeckeSeriesSphericalIntegralInverseStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumHeckeSeriesSphericalIntegralInverse
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasBoundedSumsOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumHeckeSeriesSphericalIntegralInverseStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.hasSum_hecke_series_spherical_integral_inverse : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (γ : Fin n → ℂ) (φ : GL (Fin n) k → ℂ), IsBorelSph k γ φ → (∀ i, γ i ≠ 0) → ∀ X : ℂ, (∀ i : Fin n, ‖(resCard k : ℂ) ^ (i : ℕ) * (γ i)⁻¹ * X‖ < 1) → HasSum (fun c : {c : GL (Fin n) k ⧸ KO k (Fin n) // (∀ i j, (c.out⁻¹ : GL (Fin n) k).1 i j ∈ 𝒪[k])} => X ^ (-ord k (Matrix.GeneralLinearGroup.det c.1.out)).toNat * φ c.1.out) (∏ i : Fin n, (1 - (resCard k : ℂ) ^ (i : ℕ) * (γ i)⁻¹ * X)⁻¹) := by sorry
