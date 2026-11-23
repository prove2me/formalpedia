-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_cls_rep
-- name    : GlobalTheory.CompanionTheory.RgEis.cls_rep
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:16:26.360235+00:00
-- url     : https://prove2.me/theorems/e4d367df-d3d7-43ca-9c83-b873c252a10e
-- title:
--   Rg Eis: cls rep
-- statement:
--   The Rg Eis construction uses the cls rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/StagedEstimateHolds.lean#L21-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/StagedEstimateHolds.lean#L21-L21

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

theorem GlobalTheory.CompanionTheory.RgEis.cls_rep (q : Cos P Γ) : cls ⟨rep q, rep_mem q⟩ = q := by sorry
