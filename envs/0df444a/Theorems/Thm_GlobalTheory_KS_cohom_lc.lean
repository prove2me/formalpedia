-- Prove2me | Theorems.Thm_GlobalTheory_KS_cohom_lc
-- name    : GlobalTheory.KS.cohom_lc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:52:29.860798+00:00
-- url     : https://prove2.me/theorems/45d489a4-24a9-4641-bbb1-3c62e124b925
-- title:
--   KS: cohom lc
-- statement:
--   The KS construction uses the cohom lc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/LeISupInfPreimage.lean#L150-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/LeISupInfPreimage.lean#L150-L164

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
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
open GlobalTheory GlobalTheory.KS
variable {K : Type} [Field K] {Y : Scheme.{0}} {I : Type} {U : I → Y.Opens}

theorem GlobalTheory.KS.cohom_lc (q : Y ⟶ Sp K) (f : Y ⟶ Y) (hf : f ≫ q = q) {g : ℕ} (a : Fin g → K) (c c' : Fin g → C1 U)
    (h : ∀ x, Cohom f U (c x) (c' x)) : Cohom f U (lc q a c) (lc q a c') := by sorry
