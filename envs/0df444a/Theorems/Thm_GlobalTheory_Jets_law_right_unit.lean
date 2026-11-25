-- Prove2me | Theorems.Thm_GlobalTheory_Jets_law_right_unit
-- name    : GlobalTheory.Jets.law_right_unit
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:52:23.717833+00:00
-- url     : https://prove2.me/theorems/ce570bcd-9768-4b57-afc2-ca201687e457
-- title:
--   Jets: law right unit
-- statement:
--   The Jets construction uses the law right unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/HasSubstAddSqZero.lean#L91-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/HasSubstAddSqZero.lean#L91-L108

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ContinuousPderivDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_HasSubstAddSqZero
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.Jets

theorem GlobalTheory.Jets.law_right_unit {R : Type} [CommRing R] {d : ℕ} (G : FGLaw R d) (i : Fin d) :
    ev (n := 1) ![pt R d 0, 0] (G.F i) = (X ((0 : Fin 1), i) : PS R 1 d) := by sorry
