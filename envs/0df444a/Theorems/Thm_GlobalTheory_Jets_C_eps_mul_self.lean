-- Prove2me | Theorems.Thm_GlobalTheory_Jets_C_eps_mul_self
-- name    : GlobalTheory.Jets.C_eps_mul_self
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:49:50.636152+00:00
-- url     : https://prove2.me/theorems/6f89b6b1-b60b-4624-97da-48557efe6f4d
-- title:
--   Jets: C eps mul self
-- statement:
--   The Jets construction uses the C eps mul self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/HasSubstAddSqZero.lean#L121-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/HasSubstAddSqZero.lean#L121-L123

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

theorem GlobalTheory.Jets.C_eps_mul_self (R : Type) [CommRing R] (τ : Type) :
    (C (DualNumber.eps : DualNumber R) : MvPowerSeries τ (DualNumber R)) * C DualNumber.eps = 0 := by sorry
