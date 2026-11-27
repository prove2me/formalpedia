-- Prove2me | Theorems.Thm_GroundTheory_Brauer_H2mul_mapPair_comp
-- name    : GroundTheory.Brauer.H2mul.mapPair_comp
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:54:07.907105+00:00
-- url     : https://prove2.me/theorems/0825fa1c-15e7-50fc-acd5-db4ee988a397
-- title:
--   H2mul: map Pair comp
-- statement:
--   The H2mul construction uses the map Pair comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/MulDistribMulActionQuotientFixedPoints.lean#L179-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/MulDistribMulActionQuotientFixedPoints.lean#L179-L186

import Mathlib
import Definitions.Def_GroundTheory_Brauer_MulDistribMulActionQuotientFixedPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Brauer
open groupCohomology
universe u v u' v'
variable (G : Type u) (M : Type v) [Group G] [CommGroup M] [MulDistribMulAction G M]
open GroundTheory.Brauer.H2mul
variable {G M}
variable {G' : Type u'} {M' : Type v'} [Group G'] [CommGroup M'] [MulDistribMulAction G' M']

theorem GroundTheory.Brauer.H2mul.mapPair_comp {G'' : Type*} {M'' : Type*} [Group G''] [CommGroup M'']
    [MulDistribMulAction G'' M''] (f : G' →* G) (φ : M →* M')
    (hφ : ∀ (g : G') (m : M), φ (f g • m) = g • φ m) (f' : G'' →* G') (φ' : M' →* M'')
    (hφ' : ∀ (g : G'') (m : M'), φ' (f' g • m) = g • φ' m) :
    mapPair (f.comp f') (φ'.comp φ) (fun g m => by simp [hφ, hφ']) =
      (mapPair f' φ' hφ').comp (mapPair f φ hφ) := by sorry
