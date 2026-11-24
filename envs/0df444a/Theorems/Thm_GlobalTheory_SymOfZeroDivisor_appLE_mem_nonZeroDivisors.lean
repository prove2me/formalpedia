-- Prove2me | Theorems.Thm_GlobalTheory_SymOfZeroDivisor_appLE_mem_nonZeroDivisors
-- name    : GlobalTheory.SymOfZeroDivisor.appLE_mem_nonZeroDivisors
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:02:30.128863+00:00
-- url     : https://prove2.me/theorems/811be0be-8ed9-4fea-b7de-61a262fd1de7
-- title:
--   Sym Of Zero Divisor: app LE mem non Zero Divisors
-- statement:
--   The Sym Of Zero Divisor construction uses the app LE mem non Zero Divisors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/SymmetricLineBundleOfRegularSection.lean#L10-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/SymmetricLineBundleOfRegularSection.lean#L10-L23

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_IsoLineBundleOfRegularPullbacksSameZeroSchemeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SymmetricLineBundleOfRegularSection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SymOfZeroDivisor

theorem GlobalTheory.SymOfZeroDivisor.appLE_mem_nonZeroDivisors {X Y : Scheme.{0}} (f : Y ⟶ X) [IsOpenImmersion f]
    (W : X.Opens) (a : Γ(X, W))
    (ha : ∀ (V : X.Opens) (h : V ≤ W), resG X h a ∈ nonZeroDivisors Γ(X, V))
    (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ W) : (f.appLE W V h).hom a ∈ nonZeroDivisors Γ(Y, V) := by sorry
