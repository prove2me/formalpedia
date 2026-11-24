-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_UnitaryHaarVolume_baseFr_mem
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.baseFr_mem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:15:55.950886+00:00
-- url     : https://prove2.me/theorems/558f1582-2ae2-4d0e-9b30-c58c194b638c
-- title:
--   Unitary Haar Volume: base Fr mem
-- statement:
--   The Unitary Haar Volume construction uses the base Fr mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/UnitaryHaarVolume.lean#L84-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/UnitaryHaarVolume.lean#L84-L87

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_NormsFree
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_UnitaryHaarVolume
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume
open Formalism.L2.Pj Formalism.L2.PjFree NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD MeasureTheory
open scoped ENNReal
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
set_option autoImplicit false
open NumberField MeasureTheory
open scoped ENNReal
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r)

theorem GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.baseFr_mem :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.baseFr X ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.OrthFr X := by sorry
