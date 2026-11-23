-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_connecting_connLeft
-- name    : GroundTheory.GroupCoh.connecting_connLeft
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:58:56.874201+00:00
-- url     : https://prove2.me/theorems/74d6eec6-7ed6-4817-8e80-3589270e1ffb
-- title:
--   Group Coh: connecting conn Left
-- statement:
--   The Group Coh construction uses the connecting conn Left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/HerbrandAbstract.lean#L247-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/HerbrandAbstract.lean#L247-L260

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

theorem GroundTheory.GroupCoh.connecting_connLeft (hi : Function.Injective i) (hp : Function.Surjective p)
    (hex : Function.Exact i p) (hfi : ∀ a, i (fA a) = fB (i a))
    (hgi : ∀ a, i (gA a) = gB (i a)) (hfp : ∀ b, p (fB b) = fC (p b))
    (hgp : ∀ b, p (gB b) = gC (p b)) (hfgB : ∀ b, fB (gB b) = 0) (hgfB : ∀ b, gB (fB b) = 0)
    (s : connDomain fB i) :
    connecting hi hp hex hfi hgi hfp hgp hfgB hgfB (connLeft hex hfp s) =
      (connRight hi hgi hgfB s : KerModRange gA fA) := by sorry
