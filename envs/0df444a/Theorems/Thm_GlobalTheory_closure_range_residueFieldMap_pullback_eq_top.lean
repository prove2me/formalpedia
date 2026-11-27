-- Prove2me | Theorems.Thm_GlobalTheory_closure_range_residueFieldMap_pullback_eq_top
-- name    : GlobalTheory.closure_range_residueFieldMap_pullback_eq_top
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:44:13.973674+00:00
-- url     : https://prove2.me/theorems/ad370694-ef5a-429b-b7ad-439837a0b664
-- title:
--   Global Theory: closure range residue Field Map pullback eq top
-- statement:
--   The Global Theory construction uses the closure range residue Field Map pullback eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PullbackResidueFieldsGenerate.lean#L32-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PullbackResidueFieldsGenerate.lean#L32-L70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PullbackResidueFieldsGenerate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory
open CategoryTheory Limits AlgebraicGeometry

theorem GlobalTheory.closure_range_residueFieldMap_pullback_eq_top (X Y S : Scheme.{0}) (f : X ⟶ S) (g : Y ⟶ S)
    (t : ↑(pullback f g)) :
    Subfield.closure (Set.range ((pullback.fst f g).residueFieldMap t).hom ∪
      Set.range ((pullback.snd f g).residueFieldMap t).hom) = ⊤ := by sorry
