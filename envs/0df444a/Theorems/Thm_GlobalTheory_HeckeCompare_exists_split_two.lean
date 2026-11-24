-- Prove2me | Theorems.Thm_GlobalTheory_HeckeCompare_exists_split_two
-- name    : GlobalTheory.HeckeCompare.exists_split_two
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:03:23.912395+00:00
-- url     : https://prove2.me/theorems/9b8d9136-120e-488c-9ce2-7f0894158b64
-- title:
--   Hecke Compare: exists split two
-- statement:
--   The Hecke Compare construction uses the exists split two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NatCastMemConj.lean#L45-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NatCastMemConj.lean#L45-L74

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUnimodDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NatCastMemConj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HeckeCompare

theorem GlobalTheory.HeckeCompare.exists_split_two {O : Type} [CommRing O] [IsDedekindDomain O] {p : O} (hp : p ≠ 0) (P P' : Ideal O)
    [hP : P.IsMaximal] [hP' : P'.IsMaximal] (hco : P ⊔ P' = ⊤) : ∃ (m n : ℕ) (w u v a : O), w + v + u = 1 ∧
      a ∉ P ∧ a ∉ P' ∧ p ∣ w * a ∧ (∀ b ∈ P ^ m, p ∣ u * b) ∧ ∀ b ∈ P' ^ n, p ∣ v * b := by sorry
