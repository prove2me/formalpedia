-- Prove2me | Theorems.Thm_GlobalTheory_pureType_vector_spans_quadratic_lattice
-- name    : GlobalTheory.pureType_vector_spans_quadratic_lattice
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:15:38.460192+00:00
-- url     : https://prove2.me/theorems/a0052d0a-5f15-4c50-b7b4-35ab84ef20bd
-- title:
--   Global Theory: pure Type vector spans quadratic lattice
-- statement:
--   The Global Theory construction uses the pure Type vector spans quadratic lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/PureTypeVectorSpansQuadraticLattice.lean#L40-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/PureTypeVectorSpansQuadraticLattice.lean#L40-L124

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_PureTypeVectorSpansQuadraticLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open scoped CategoryTheory.Obj

theorem GlobalTheory.pureType_vector_spans_quadratic_lattice :
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Pe : D.La →+ (Fin g → ℂ))
    (Hm : Matrix (Fin g) (Fin g) ℂ), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod D ty Pe → Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z z).re) →
  (∀ x y, (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (Pe x) (Pe y)).im = D.EF x y) →
  ∀ (ρ : ℂ) (a : D.La), ρ ^ 2 = -(H.d : ℂ) → (∀ i, ty i (H.rt : E) ≠ ρ → Pe a i = 0) →
  (∀ m n : ℤ, ((m : ℂ) + n * ((1 + Complex.I * Real.sqrt H.d) / 2)) • Pe a ∈ Pe.range) ∧
  ∀ z w : ℂ, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (z • Pe a) (w • Pe a) = ((D.EF (H.w0 • a) a).natAbs : ℂ) * (2 * z * starRingEnd ℂ w / Real.sqrt H.d) := by sorry
