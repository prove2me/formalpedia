-- Prove2me | Theorems.Thm_GlobalTheory_SplitSpread_map_gen
-- name    : GlobalTheory.SplitSpread.map_gen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:31:00.20996+00:00
-- url     : https://prove2.me/theorems/c5052f77-2a36-47f0-b2a2-4e6d5ba8eb26
-- title:
--   Split Spread: map gen
-- statement:
--   The Split Spread construction uses the map gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SplittingAbsenceSpreads.lean#L40-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SplittingAbsenceSpreads.lean#L40-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NoCommonZeroSpreadsConstructibleNbhdStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SplittingAbsenceSpreads
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
open GlobalTheory GlobalTheory.SplitSpread
open MvPolynomial
variable {σ : Type} [Finite σ] (A : Type) [CommRing A] (D : ℕ)
variable {A D}

theorem GlobalTheory.SplitSpread.map_gen {k : Type} [CommRing k] (ψ : A →+* k) (z : Var σ D → k) (b : Bool) :
    MvPolynomial.map (eval₂Hom ψ z) (gen A D b) = ∑ m : Mon σ D, monomial m.1 (z (Sum.inl (b, m))) := by sorry
