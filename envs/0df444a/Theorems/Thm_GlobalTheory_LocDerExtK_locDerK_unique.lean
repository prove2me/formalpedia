-- Prove2me | Theorems.Thm_GlobalTheory_LocDerExtK_locDerK_unique
-- name    : GlobalTheory.LocDerExtK.locDerK_unique
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:37:24.405798+00:00
-- url     : https://prove2.me/theorems/e494555e-1b37-4741-ba73-bb4adcca8714
-- title:
--   Loc Der Ext K: loc Der K unique
-- statement:
--   The Loc Der Ext K construction uses the loc Der K unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniqueLocalDerivationAlongFibreFieldOfAffi.lean#L93-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniqueLocalDerivationAlongFibreFieldOfAffi.lean#L93-L104

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLocalDerivationExtensionOfAffine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueLocalDerivationAlongFibreFieldOfAffi
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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.LocDerExtK
open GlobalTheory.LocDerExt

theorem GlobalTheory.LocDerExtK.locDerK_unique {K : Type} [Field K] {R : Type} [CommRing R] {Y X : Scheme.{0}} {q : Y ⟶ Sp K}
    {p : X ⟶ Sp R} {m : Y ⟶ X} {D : R → K} {W₀ : X.Opens} (hW : IsAffineOpen W₀)
    (d d' : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)) (h : LocDerK q p m D W₀ d)
    (h' : LocDerK q p m D W₀ d') (e : d W₀ = d' W₀) (W : X.Opens) (hle : W ≤ W₀) : d W = d' W := by sorry
