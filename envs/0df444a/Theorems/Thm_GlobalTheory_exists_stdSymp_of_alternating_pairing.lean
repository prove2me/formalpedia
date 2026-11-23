-- Prove2me | Theorems.Thm_GlobalTheory_exists_stdSymp_of_alternating_pairing
-- name    : GlobalTheory.exists_stdSymp_of_alternating_pairing
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:26:49.133846+00:00
-- url     : https://prove2.me/theorems/ba074bd7-2b9b-4f76-8ee0-f3b9a7cc968c
-- title:
--   Global Theory: exists std Symp of alternating pairing
-- statement:
--   The Global Theory construction uses the exists std Symp of alternating pairing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsStdSympZmod.lean#L172-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsStdSympZmod.lean#L172-L206

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsStdSympZmod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Out

theorem GlobalTheory.exists_stdSymp_of_alternating_pairing :
    ∀ (M g : ℕ) (G : Type) [CommGroup G] (R : Type) [CommRing R] [IsDomain R] (ζ : Rˣ), 0 < M →
    IsPrimitiveRoot ζ M → (∀ x : G, x ^ M = 1) →
    (∀ d : ℕ, d ∣ M → Nat.card {x : G // x ^ d = 1} = d ^ (2 * g)) →
    ∀ e : G →* G →* Rˣ, (∀ x, e x x = 1) → (∀ x, (∀ y, e x y = 1) → x = 1) →
    ∃ x : Fin (2 * g) → G, ∀ i j, e (x i) (x j) = ζ ^ stdSymp g i j := by sorry
