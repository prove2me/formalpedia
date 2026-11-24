-- Prove2me | Theorems.Thm_GlobalTheory_SquareDensity_eq_zero_of_sq
-- name    : GlobalTheory.SquareDensity.eq_zero_of_sq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:24:23.592493+00:00
-- url     : https://prove2.me/theorems/d331a1b5-4e1b-4c97-b491-af34dbb149f8
-- title:
--   Square Density: eq zero of sq
-- statement:
--   The Square Density construction uses the eq zero of sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSqAddSubDvd.lean#L51-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSqAddSubDvd.lean#L51-L111

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSqAddSubDvd
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
open GlobalTheory
open GlobalTheory.SquareDensity

theorem GlobalTheory.SquareDensity.eq_zero_of_sq {K : Type*} [Field K] [CharZero K] (Ψ : Polynomial ℤ → K) (d : ℕ)
    (hΨ : ∀ r : ℕ, ∃ Φ : MvPolynomial (Fin r) K, Φ.totalDegree ≤ d ∧
      ∀ F : Polynomial ℤ, F.natDegree < r →
        Ψ F = MvPolynomial.eval (fun i : Fin r => ((F.coeff i : ℤ) : K)) Φ)
    (hsq : ∀ G, Ψ (G ^ 2) = 0) (F : Polynomial ℤ) : Ψ F = 0 := by sorry
