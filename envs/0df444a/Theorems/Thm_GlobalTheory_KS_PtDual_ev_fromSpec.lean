-- Prove2me | Theorems.Thm_GlobalTheory_KS_PtDual_ev_fromSpec
-- name    : GlobalTheory.KS.PtDual.ev_fromSpec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:24:04.95905+00:00
-- url     : https://prove2.me/theorems/2f2b8e09-5de8-4da5-b457-94acf9562620
-- title:
--   Pt Dual: ev from Spec
-- statement:
--   The Pt Dual construction uses the ev from Spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/GermDerivationIffDualNumberPoint.lean#L21-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/GermDerivationIffDualNumberPoint.lean#L21-L25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GermDerivationIffDualNumberPoint
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
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.PtDual
variable {X : Scheme.{0}} {R S : Type} [CommRing R] [CommRing S]

theorem GlobalTheory.KS.PtDual.ev_fromSpec (v : Sp R ⟶ X) {U : X.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ v ⁻¹ᵁ U) :
    Spec.map (CommRingCat.ofHom (ev v U h)) ≫ hU.fromSpec = v := by sorry
