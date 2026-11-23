-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_cls_eq
-- name    : GlobalTheory.CompanionTheory.RgEis.cls_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:16:48.965804+00:00
-- url     : https://prove2.me/theorems/a8cffed6-2a1e-4627-a969-69dc0f3ed056
-- title:
--   Rg Eis: cls eq
-- statement:
--   The Rg Eis construction uses the cls eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/StagedEstimateHolds.lean#L12-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/StagedEstimateHolds.lean#L12-L17

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

theorem GlobalTheory.CompanionTheory.RgEis.cls_eq {a b : Γ} : (cls a : Cos P Γ) = cls b ↔ (b : G) * (a : G)⁻¹ ∈ P := by sorry
