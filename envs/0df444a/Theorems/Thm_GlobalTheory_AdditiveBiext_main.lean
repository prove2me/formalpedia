-- Prove2me | Theorems.Thm_GlobalTheory_AdditiveBiext_main
-- name    : GlobalTheory.AdditiveBiext.main
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:37:06.457141+00:00
-- url     : https://prove2.me/theorems/f0d6ebb9-b156-4dc9-813f-fd7b62ff5971
-- title:
--   Additive Biext: main
-- statement:
--   The Additive Biext construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/Comp1Scalar.lean#L44-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/Comp1Scalar.lean#L44-L46

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasSubstEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_Comp1Scalar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
noncomputable section
open GlobalTheory GlobalTheory.AdditiveBiext
variable {R : Type} [CommRing R] {d : ℕ}

theorem GlobalTheory.AdditiveBiext.main : ∀ (R : Type) [CommRing R] [StarRing R] (d : ℕ), ∃ B : FB R d R,
    (∀ i, B.G.F i = X ((0 : Fin 2), i) + X ((1 : Fin 2), i)) ∧ ∀ a i, B.A.act a i = C a * X ((0 : Fin 1), i) := by sorry
