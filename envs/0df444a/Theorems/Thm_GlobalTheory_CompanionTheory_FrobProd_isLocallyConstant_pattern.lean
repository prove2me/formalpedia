-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FrobProd_isLocallyConstant_pattern
-- name    : GlobalTheory.CompanionTheory.FrobProd.isLocallyConstant_pattern
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:18.026649+00:00
-- url     : https://prove2.me/theorems/5cd6a322-33f9-4094-b927-f6d5475eea89
-- title:
--   Frob Prod: is Locally Constant pattern
-- statement:
--   The Frob Prod construction uses the is Locally Constant pattern property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SchwartzBruhatProdSpanTensors.lean#L29-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SchwartzBruhatProdSpanTensors.lean#L29-L44

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_SupportedInIffOfFrob
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SchwartzBruhatProdSpanTensors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FrobProd
open Classical

theorem GlobalTheory.CompanionTheory.FrobProd.isLocallyConstant_pattern {X ι : Type} [TopologicalSpace X] [Fintype ι] {U : ι → Set X}
    (hU : ∀ i, IsClopen (U i)) :
    IsLocallyConstant (fun x => Finset.univ.filter (fun i => x ∈ U i)) := by sorry
