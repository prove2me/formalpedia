-- Prove2me | Theorems.Thm_GlobalTheory_Jets_hasSubst_add_sqZero
-- name    : GlobalTheory.Jets.hasSubst_add_sqZero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:52:21.548966+00:00
-- url     : https://prove2.me/theorems/4c44dcb2-bb3a-47c8-99c6-0d7aab099f7c
-- title:
--   Jets: has Subst add sq Zero
-- statement:
--   The Jets construction uses the has Subst add sq Zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/HasSubstAddSqZero.lean#L13-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/HasSubstAddSqZero.lean#L13-L20

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

theorem GlobalTheory.Jets.hasSubst_add_sqZero {σ τ S : Type} [Fintype σ] [CommRing S]
    (a b : σ → MvPowerSeries τ S) (e : MvPowerSeries τ S) (he : e * e = 0)
    (ha : ∀ s, IsNilpotent (constantCoeff (a s))) : HasSubst (fun s => a s + e * b s) := by sorry
