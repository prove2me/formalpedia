-- Prove2me | Theorems.Thm_GlobalTheory_SympBasis_eq_of_sum_stdSymp
-- name    : GlobalTheory.SympBasis.eq_of_sum_stdSymp
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:24:51.70148+00:00
-- url     : https://prove2.me/theorems/e1bb4c87-87bb-4294-a58b-eef8cfd07b11
-- title:
--   Symp Basis: eq of sum std Symp
-- statement:
--   The Symp Basis construction uses the eq of sum std Symp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SymplecticTorsionSystemIsGeometricBasis.lean#L42-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SymplecticTorsionSystemIsGeometricBasis.lean#L42-L54

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SymplecticTorsionSystemIsGeometricBasis
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
open GlobalTheory GlobalTheory.SympBasis

theorem GlobalTheory.SympBasis.eq_of_sum_stdSymp {R : Type} [CommRing R] {g : ℕ} (a b : Fin (2 * g) → R)
    (h : ∀ j, ∑ i, a i * (Out.stdSymp g i j : R) = ∑ i, b i * (Out.stdSymp g i j : R)) : a = b := by sorry
