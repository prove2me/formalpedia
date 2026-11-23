-- Prove2me | Theorems.Thm_GlobalTheory_KS_VertFib_ringVal_spMap
-- name    : GlobalTheory.KS.VertFib.ringVal_spMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:34:23.454639+00:00
-- url     : https://prove2.me/theorems/9a06fd17-6219-496d-b057-559c2cdd1cc6
-- title:
--   Vert Fib: ring Val sp Map
-- statement:
--   The Vert Fib construction uses the ring Val sp Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/GermDerivationOfFibreOfKillsBase.lean#L56-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/GermDerivationOfFibreOfKillsBase.lean#L56-L62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GermDerivationIffDualNumberPointStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GermDerivationOfFibreOfKillsBase
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
noncomputable section
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.VertFib

theorem GlobalTheory.KS.VertFib.ringVal_spMap {A R : Type} [CommRing A] [CommRing R] (φ : R →+* A) (h : ⊤ ≤ spMap φ ⁻¹ᵁ ⊤) (s : Γ(Sp R, ⊤)) :
    ringVal (spMap φ) ⊤ h s = φ ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom s) := by sorry
