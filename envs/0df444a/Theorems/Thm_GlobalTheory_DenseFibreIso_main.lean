-- Prove2me | Theorems.Thm_GlobalTheory_DenseFibreIso_main
-- name    : GlobalTheory.DenseFibreIso.main
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:55:31.629239+00:00
-- url     : https://prove2.me/theorems/08b33d5b-2664-4e84-8325-6e3deace9db9
-- title:
--   Dense Fibre Iso: main
-- statement:
--   The Dense Fibre Iso construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsAwaySurjective.lean#L225-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsAwaySurjective.lean#L225-L276

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsAwaySurjective
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
open GlobalTheory GlobalTheory.DenseFibreIso
set_option backward.isDefEq.respectTransparency.types false

theorem GlobalTheory.DenseFibreIso.main : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Γ' X : Scheme.{0}) (s : X ⟶ Sp R) (f : Γ' ⟶ X) (P : Set (Ideal R)), (∀ (q₀ : Ideal R) (f₀ : R), q₀.IsPrime → f₀ ∉ q₀ → ∃ p₀ ∈ P, p₀.IsPrime ∧ q₀ ≤ p₀ ∧ f₀ ∉ p₀) → IsProper s → Flat s → IsProper f → Flat (f ≫ s) → (∀ q ∈ P, ∃ (K : Type) (_ : Field K) (x : R →+* K), RingHom.ker x = q ∧ IsIso (pullback.snd f (pullback.fst s (spMap x)))) → IsIso f := by sorry
