-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_BB_RatCoord_ofF_bijective
-- name    : GlobalTheory.CompanionTheory.SW.BB.RatCoord.ofF_bijective
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:00:56.442797+00:00
-- url     : https://prove2.me/theorems/4fd607a9-7e96-465d-b77b-4fade9f7257c
-- title:
--   Rat Coord: of F bijective
-- statement:
--   The Rat Coord construction uses the of F bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/CoordinateBijectionTraceForm.lean#L18-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/CoordinateBijectionTraceForm.lean#L18-L30

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussQ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateBijectionTraceForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB GlobalTheory.CompanionTheory.SW.BB.RatCoord
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem GlobalTheory.CompanionTheory.SW.BB.RatCoord.ofF_bijective {F E : Type} [Field F] [Field E] [Algebra F E] {d M : ℕ}
    (b : Module.Basis (Fin d) F E) :
    Function.Bijective (ofF b : (Fin M × Fin d → F) → Fin 1 → Fin M → E) := by sorry
