-- Prove2me | Theorems.Thm_GlobalTheory_T_exteriorFormsSpanOfSets_mul_smul_mono
-- name    : GlobalTheory.T.exteriorFormsSpanOfSets_mul_smul_mono
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:40:25.524267+00:00
-- url     : https://prove2.me/theorems/542fa421-7101-4b44-a084-cb77c7c485cc
-- title:
--   T: exterior Forms Span Of Sets mul smul mono
-- statement:
--   The T construction uses the exterior Forms Span Of Sets mul smul mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExteriorFormsSpanOfSetsMulSmulMonoStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExteriorFormsSpanOfSetsMulSmulMonoStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExteriorFormsSpanOfSetsMulSmulMono
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExteriorFormsSpanOfSetsMulSmulMonoStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exteriorFormsSpanOfSets_mul_smul_mono : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] (A : Subring K) (L : Set V), (1 : ExteriorAlgebra K V) ∈ forms (A : Set K) L 0 ∧ (∀ q x y, x ∈ forms (A : Set K) L 1 → y ∈ forms (A : Set K) L q → x * y ∈ forms (A : Set K) L (q + 1)) ∧ (∀ q (c : K) y, c ∈ A → y ∈ forms (A : Set K) L q → c • y ∈ forms (A : Set K) L q) ∧ (∀ (B : Set K) q (c : K) y, y ∈ forms B L q → c • y ∈ forms ((fun b => c * b) '' B) L q) ∧ ∀ (B B' : Set K) (L' : Set V) q, B ⊆ B' → L ⊆ L' → forms B L q ≤ forms B' L' q := by sorry
