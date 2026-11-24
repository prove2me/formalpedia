-- Prove2me | Theorems.Thm_GlobalTheory_NearlyPrimitive_dpow_add
-- name    : GlobalTheory.NearlyPrimitive.dpow_add
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:32:03.441379+00:00
-- url     : https://prove2.me/theorems/4fc6c7a5-eabf-4750-bae2-3ba213d6a55b
-- title:
--   Nearly Primitive: dpow add
-- statement:
--   The Nearly Primitive construction uses the dpow add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NormSmulLeOneOfPrimitiveBoundedPowers.lean#L63-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NormSmulLeOneOfPrimitiveBoundedPowers.lean#L63-L80

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NormSmulLeOneOfPrimitiveBoundedPowers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.NearlyPrimitive
open Finset Filter Topology

theorem GlobalTheory.NearlyPrimitive.dpow_add {C : Type} [Field C] [CharZero C] {B : Type} [CommRing B] [Algebra C B]
    (n : ℕ) (x y : B) :
    dpow C n (x + y) = ∑ m ∈ antidiagonal n, dpow C m.1 x * dpow C m.2 y := by sorry
