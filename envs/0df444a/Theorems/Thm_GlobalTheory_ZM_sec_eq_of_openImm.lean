-- Prove2me | Theorems.Thm_GlobalTheory_ZM_sec_eq_of_openImm
-- name    : GlobalTheory.ZM.sec_eq_of_openImm
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:02:32.485848+00:00
-- url     : https://prove2.me/theorems/6ddf376d-7475-4aae-ab0a-bcd1d481471b
-- title:
--   ZM: sec eq of open Imm
-- statement:
--   The ZM construction uses the sec eq of open Imm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsSectionCoordinateVectorOfLocallyOnRing.lean#L25-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsSectionCoordinateVectorOfLocallyOnRing.lean#L25-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsSectionCoordinateVectorOfLocallyOnRing
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
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.ZM

theorem GlobalTheory.ZM.sec_eq_of_openImm {Y : Scheme.{0}} (W : Y.Opens) (s t : Γ(Y, W))
    (H : ∀ p ∈ W, ∃ (Z : Scheme.{0}) (f : Z ⟶ Y) (_ : IsOpenImmersion f) (z : Z) (W' : Z.Opens)
      (h : W' ≤ f ⁻¹ᵁ W), z ∈ W' ∧ f z = p ∧ (f.appLE W W' h).hom s = (f.appLE W W' h).hom t) : s = t := by sorry
