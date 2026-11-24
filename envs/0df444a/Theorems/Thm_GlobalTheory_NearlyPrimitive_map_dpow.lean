-- Prove2me | Theorems.Thm_GlobalTheory_NearlyPrimitive_map_dpow
-- name    : GlobalTheory.NearlyPrimitive.map_dpow
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:31:45.618685+00:00
-- url     : https://prove2.me/theorems/e8dbe70e-6cfe-4590-bf31-d5bda1ee7a70
-- title:
--   Nearly Primitive: map dpow
-- statement:
--   The Nearly Primitive construction uses the map dpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NormSmulLeOneOfPrimitiveBoundedPowers.lean#L82-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NormSmulLeOneOfPrimitiveBoundedPowers.lean#L82-L84

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

theorem GlobalTheory.NearlyPrimitive.map_dpow {C : Type} [Field C] {B B' : Type} [CommRing B] [Algebra C B] [CommRing B']
    [Algebra C B'] (f : B →ₐ[C] B') (n : ℕ) (x : B) : f (dpow C n x) = dpow C n (f x) := by sorry
