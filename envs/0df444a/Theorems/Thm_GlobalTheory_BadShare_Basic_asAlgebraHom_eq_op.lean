-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_Basic_asAlgebraHom_eq_op
-- name    : GlobalTheory.BadShare.Basic.asAlgebraHom_eq_op
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:56:36.553881+00:00
-- url     : https://prove2.me/theorems/7207468a-e898-4fc4-bd7b-8fd0b2e7c390
-- title:
--   Basic: as Algebra Hom eq op
-- statement:
--   The Basic construction uses the as Algebra Hom eq op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/StandardFiveNontrivial.lean#L330-L332
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/StandardFiveNontrivial.lean#L330-L332

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

theorem GlobalTheory.BadShare.Basic.asAlgebraHom_eq_op {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M) (a : MonoidAlgebra ℂ G) :
    ρ.asAlgebraHom a = op ρ (fun x => a.coeff x) := by sorry
