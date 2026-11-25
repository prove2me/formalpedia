-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_tateCup_connecting_left
-- name    : GroundTheory.GroupCoh.tateCup_connecting_left
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:52:16.375358+00:00
-- url     : https://prove2.me/theorems/8ce9c39d-46d4-486c-bfdf-fcfb50399f87
-- title:
--   Group Coh: tate Cup connecting left
-- statement:
--   The Group Coh construction uses the tate Cup connecting left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupTateShift.lean#L276-L326
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupTateShift.lean#L276-L326

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_AugmentationSES
import Definitions.Def_GroundTheory_TateCohomology_TateConnecting
import Definitions.Def_GroundTheory_TateCohomology_TateLow
import Definitions.Def_GroundTheory_TateCohomology_CupTateShift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory MonoidalCategory groupCohomology
open GroundTheory GroundTheory.GroupCoh
universe u
variable {k G : Type u} [CommRing k] [Group G]
variable [Fintype G]
set_option maxHeartbeats 1600000

theorem GroundTheory.GroupCoh.tateCup_connecting_left (m : ℕ) : ∀ (p q : ℤ), (1 - p).toNat + (1 - q).toNat = m →
    ∀ {E : ShortComplex (Rep.{u} k G)} (hE : E.ShortExact) (B : Rep.{u} k G)
      (hEB : (E.map (tensorRight B)).ShortExact) (r : ℤ) (h : p + q = r)
      (a : tateCohomology E.X₃ p) (b : tateCohomology B q),
      (tδ hEB r (r + 1) rfl).hom (tateCup p q E.X₃ B r h a b) =
        tateCup (p + 1) q E.X₁ B (r + 1) (by omega) ((tδ hE p (p + 1) rfl).hom a) b := by sorry
