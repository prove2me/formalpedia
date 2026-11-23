-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_Basic_op_eq_asAlgebraHom
-- name    : GlobalTheory.BadShare.Basic.op_eq_asAlgebraHom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:55:03.909564+00:00
-- url     : https://prove2.me/theorems/9840f2ce-49e2-4c50-9252-5340dd46e6a9
-- title:
--   Basic: op eq as Algebra Hom
-- statement:
--   The Basic construction uses the op eq as Algebra Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/StandardFiveNontrivial.lean#L326-L328
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/StandardFiveNontrivial.lean#L326-L328

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_StandardFiveNontrivial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Classical
open GlobalTheory GlobalTheory.BadShare
variable (g : ℕ) [Fact g.Prime] (N : ℕ)
variable {g N}
open GlobalTheory.BadShare.Basic
variable {G : Type} [Group G] [Fintype G]

theorem GlobalTheory.BadShare.Basic.op_eq_asAlgebraHom {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M) (e : G → ℂ) :
    op ρ e = ρ.asAlgebraHom (alg e) := by sorry
