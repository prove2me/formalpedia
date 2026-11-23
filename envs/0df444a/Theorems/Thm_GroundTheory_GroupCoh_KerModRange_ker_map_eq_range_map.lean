-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_KerModRange_ker_map_eq_range_map
-- name    : GroundTheory.GroupCoh.KerModRange.ker_map_eq_range_map
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:08:42.001873+00:00
-- url     : https://prove2.me/theorems/01f834b2-304b-44c0-b25b-bf8f7bd23060
-- title:
--   Ker Mod Range: ker map eq range map
-- statement:
--   The Ker Mod Range construction uses the ker map eq range map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/HerbrandAbstract.lean#L130-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/HerbrandAbstract.lean#L130-L163

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.GroupCoh
variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  {fA gA : A →+ A} {fB gB : B →+ B} {fC gC : C →+ C} {i : A →+ B} {p : B →+ C}

theorem GroundTheory.GroupCoh.KerModRange.ker_map_eq_range_map (hi : Function.Injective i)
    (hp : Function.Surjective p) (hex : Function.Exact i p)
    (hfi : ∀ a, i (fA a) = fB (i a)) (hgi : ∀ a, i (gA a) = gB (i a))
    (hfp : ∀ b, p (fB b) = fC (p b)) (hgp : ∀ b, p (gB b) = gC (p b))
    (hfgB : ∀ b, fB (gB b) = 0) :
    (KerModRange.map p hfp hgp).ker = (KerModRange.map i hfi hgi).range := by sorry
