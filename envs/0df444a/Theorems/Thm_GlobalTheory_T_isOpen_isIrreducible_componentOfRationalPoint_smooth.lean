-- Prove2me | Theorems.Thm_GlobalTheory_T_isOpen_isIrreducible_componentOfRationalPoint_smooth
-- name    : GlobalTheory.T.isOpen_isIrreducible_componentOfRationalPoint_smooth
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:41:42.105535+00:00
-- url     : https://prove2.me/theorems/2964b3d4-b3cc-48c7-bbb4-9efdafeba02c
-- title:
--   T: is Open is Irreducible component Of Rational Point smooth
-- statement:
--   The T construction uses the is Open is Irreducible component Of Rational Point smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOpenIsIrreducibleComponentOfRationalPointSmootStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOpenIsIrreducibleComponentOfRationalPointSmootStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenIsIrreducibleComponentOfRationalPointSmoot
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenIsIrreducibleComponentOfRationalPointSmootStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isOpen_isIrreducible_componentOfRationalPoint_smooth : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k)) (e : Spec (CommRingCat.of k) ⟶ X), Smooth f → e ≫ f = 𝟙 _ → IsOpen {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} ∧ IsIrreducible {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} := by sorry
