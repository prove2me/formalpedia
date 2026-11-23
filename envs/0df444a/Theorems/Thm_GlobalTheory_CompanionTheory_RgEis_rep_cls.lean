-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_rep_cls
-- name    : GlobalTheory.CompanionTheory.RgEis.rep_cls
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:28:23.767799+00:00
-- url     : https://prove2.me/theorems/bc59164f-721a-473e-85f2-47de85a234eb
-- title:
--   Rg Eis: rep cls
-- statement:
--   The Rg Eis construction uses the rep cls property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/StagedEstimateHolds.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/StagedEstimateHolds.lean#L23-L25

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_StagedEstimateHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEis
open PositivityTheory.RgEis
variable {G : Type} [Group G] {P Δ Γ : Subgroup G}

theorem GlobalTheory.CompanionTheory.RgEis.rep_cls (y : Γ) : ∃ p ∈ P, p ∈ Γ ∧ rep (cls y : Cos P Γ) = p * y := by sorry
