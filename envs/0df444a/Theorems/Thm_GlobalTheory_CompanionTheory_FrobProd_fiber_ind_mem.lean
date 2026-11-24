-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FrobProd_fiber_ind_mem
-- name    : GlobalTheory.CompanionTheory.FrobProd.fiber_ind_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:42:56.698161+00:00
-- url     : https://prove2.me/theorems/9dbbe2c8-cda0-48c8-a875-ee9661142474
-- title:
--   Frob Prod: fiber ind mem
-- statement:
--   The Frob Prod construction uses the fiber ind mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SchwartzBruhatProdSpanTensors.lean#L19-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SchwartzBruhatProdSpanTensors.lean#L19-L25

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

theorem GlobalTheory.CompanionTheory.FrobProd.fiber_ind_mem {X S : Type} [TopologicalSpace X] [T2Space X] {ξ : X → S}
    (hξ : IsLocallyConstant ξ) (s : S) (hs : IsCompact (ξ ⁻¹' {s})) :
    (fun x => if ξ x = s then (1 : ℂ) else 0) ∈ SB X := by sorry
