-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_ConjVol_integral_conj_of_md
-- name    : GlobalTheory.RootEx.ConjVol.integral_conj_of_md
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:24:48.950848+00:00
-- url     : https://prove2.me/theorems/2191559d-49c2-41f7-9bb2-62ef468f65ac
-- title:
--   Conj Vol: integral conj of md
-- statement:
--   The Conj Vol construction uses the integral conj of md property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MemNormalizerOfTri.lean#L41-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MemNormalizerOfTri.lean#L41-L48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_WeilFormulaRootExchangeParabolicIntersection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemNormalizerOfTri
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
open scoped NNReal
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.ConjVol
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (U : Subgroup G) [MeasurableSpace U] [BorelSpace U] [LocallyCompactSpace U]

theorem GlobalTheory.RootEx.ConjVol.integral_conj_of_md (μ : Measure U) [μ.IsHaarMeasure] [μ.Regular]
    (g : Subgroup.normalizer (U : Set G)) (hg : md U g = 1) (f : G → ℂ) :
    ∫ u : U, f (g * (u : G) * (g : G)⁻¹) ∂μ = ∫ u : U, f u ∂μ := by sorry
