-- Prove2me | Theorems.Thm_GlobalTheory_exists_multigraded_hilbertPoly
-- name    : GlobalTheory.exists_multigraded_hilbertPoly
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:57:21.323845+00:00
-- url     : https://prove2.me/theorems/850374bf-aa37-53b5-87c7-63325827c9f5
-- title:
--   Global Theory: exists multigraded hilbert Poly
-- statement:
--   The Global Theory construction uses the exists multigraded hilbert Poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsMultigradedHilbertPoly.lean#L426-L427
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsMultigradedHilbertPoly.lean#L426-L427

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsMultigradedHilbertPoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem GlobalTheory.exists_multigraded_hilbertPoly : ∀ (K σ : Type) [Field K] [Finite σ] (r : ℕ) (col : σ → Fin r) (I : Ideal (MvPolynomial σ K)), (∀ F ∈ I, ∀ n : Fin r → ℕ, MvPolynomial.weightedHomogeneousComponent (fun i => (Pi.single (col i) 1 : Fin r → ℕ)) n F ∈ I) → ∃ (Φ : MvPolynomial (Fin r) ℚ) (n₀ : ℕ), ∀ n : Fin r → ℕ, (∀ k, n₀ ≤ n k) → ((Module.finrank K ↥(MvPolynomial.weightedHomogeneousSubmodule K (fun i => (Pi.single (col i) 1 : Fin r → ℕ)) n) : ℕ) : ℚ) - ((Module.finrank K ↥(MvPolynomial.weightedHomogeneousSubmodule K (fun i => (Pi.single (col i) 1 : Fin r → ℕ)) n ⊓ I.restrictScalars K) : ℕ) : ℚ) = MvPolynomial.eval (fun k => (n k : ℚ)) Φ := by sorry
