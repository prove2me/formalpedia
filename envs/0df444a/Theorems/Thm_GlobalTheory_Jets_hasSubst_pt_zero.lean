-- Prove2me | Theorems.Thm_GlobalTheory_Jets_hasSubst_pt_zero
-- name    : GlobalTheory.Jets.hasSubst_pt_zero
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:49:48.857145+00:00
-- url     : https://prove2.me/theorems/dc4328ff-d581-42f8-999c-c8ade3e5dc64
-- title:
--   Jets: has Subst pt zero
-- statement:
--   The Jets construction uses the has Subst pt zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/HasSubstAddSqZero.lean#L85-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/HasSubstAddSqZero.lean#L85-L89

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

theorem GlobalTheory.Jets.hasSubst_pt_zero (R : Type) [CommRing R] (d : ℕ) :
    ∀ p : Fin 2 × Fin d,
      constantCoeff ((![pt R d 0, 0] : Fin 2 → Pt R 1 d) p.1 p.2) = 0 := by sorry
