-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_ConjVol_md_conj
-- name    : GlobalTheory.RootEx.ConjVol.md_conj
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:23:59.260606+00:00
-- url     : https://prove2.me/theorems/d369595c-997b-4db4-9155-d765bd7bd2f0
-- title:
--   Conj Vol: md conj
-- statement:
--   The Conj Vol construction uses the md conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MemNormalizerOfTri.lean#L38-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MemNormalizerOfTri.lean#L38-L39

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

theorem GlobalTheory.RootEx.ConjVol.md_conj (x g : Subgroup.normalizer (U : Set G)) : md U (x * g * x⁻¹) = md U g := by sorry
