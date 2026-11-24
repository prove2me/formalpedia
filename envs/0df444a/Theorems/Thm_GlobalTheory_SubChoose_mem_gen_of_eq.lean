-- Prove2me | Theorems.Thm_GlobalTheory_SubChoose_mem_gen_of_eq
-- name    : GlobalTheory.SubChoose.mem_gen_of_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:22:39.928259+00:00
-- url     : https://prove2.me/theorems/a3e6255b-e4e5-43ea-8739-2bf23df94a3a
-- title:
--   Sub Choose: mem gen of eq
-- statement:
--   The Sub Choose construction uses the mem gen of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFiniteSetsSubalgebraFiniteAffineCover.lean#L23-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFiniteSetsSubalgebraFiniteAffineCover.lean#L23-L40

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubNatCompSubIncl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AffineInterFiniteBasicOpenCoverStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemAdjoinRestrictedSectionsOfLocalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteSetsSubalgebraFiniteAffineCover
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub
open GlobalTheory GlobalTheory.SubChoose

theorem GlobalTheory.SubChoose.mem_gen_of_eq {X : Scheme.{0}} (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F)
    {U : X.Opens} (h : Γ(X, U)) (T : Set (F.obj (op U))) {a : F.obj (op U)} (ha : a ∈ T)
    (z : F.obj (op (X.basicOpen h))) (n : ℕ)
    (e : z * ((α.app (op (X.basicOpen h))).hom
      (X.presheaf.map (homOfLE (X.basicOpen_le h)).op h)) ^ n =
        (F.map (homOfLE (X.basicOpen_le h)).op).hom a) :
    z ∈ gen F α (X.basicOpen_le h) T := by sorry
