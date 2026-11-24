-- Prove2me | Theorems.Thm_GlobalTheory_LocBounded_isIntegral_mul_of_commute
-- name    : GlobalTheory.LocBounded.isIntegral_mul_of_commute
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:12:30.459124+00:00
-- url     : https://prove2.me/theorems/e0cc7d82-9889-4571-bad9-3e1312518041
-- title:
--   Loc Bounded: is Integral mul of commute
-- statement:
--   The Loc Bounded construction uses the is Integral mul of commute property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BoundedOfIsIntegral.lean#L10-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BoundedOfIsIntegral.lean#L10-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RootsCharpolyPowEqMapPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BoundedOfIsIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial
noncomputable section
open GlobalTheory GlobalTheory.LocBounded

theorem GlobalTheory.LocBounded.isIntegral_mul_of_commute {R A : Type} [CommRing R] [Ring A] [Algebra R A] {x y : A}
    (hc : Commute x y) (hx : IsIntegral R x) (hy : IsIntegral R y) : IsIntegral R (x * y) := by sorry
