-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_ConjVol_md_ne_zero
-- name    : GlobalTheory.RootEx.ConjVol.md_ne_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:23:48.4689+00:00
-- url     : https://prove2.me/theorems/66dbf838-09a7-45f8-be1e-9b620e5e4213
-- title:
--   Conj Vol: md ne zero
-- statement:
--   The Conj Vol construction uses the md ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MemNormalizerOfTri.lean#L36-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MemNormalizerOfTri.lean#L36-L36

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

theorem GlobalTheory.RootEx.ConjVol.md_ne_zero (g : Subgroup.normalizer (U : Set G)) : md U g ≠ 0 := by sorry
