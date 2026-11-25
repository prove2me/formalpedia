-- Prove2me | Theorems.Thm_GlobalTheory_ThetaSpecialise_exists_ratio
-- name    : GlobalTheory.ThetaSpecialise.exists_ratio
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:18:31.241808+00:00
-- url     : https://prove2.me/theorems/37a7b048-14fd-4b36-babd-6b2a85da66cf
-- title:
--   Theta Specialise: exists ratio
-- statement:
--   The Theta Specialise construction uses the exists ratio property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsMoveMap.lean#L31-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsMoveMap.lean#L31-L67

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExpansionBijectiveOverFields
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsAtTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PowEqOneOfPush
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ThetaGrpActsLinearly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsMoveMap
import Theorems.Thm_GlobalTheory_ThetaAct_exists_ratio

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaSpecialise
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange
variable {S F F' N V V' : Type} [CommRing S] [IsDomain S] [ValuationRing S] [Field F] [Field F']
  [AddCommGroup N] [Module S N] [AddCommGroup V] [Module F V] [AddCommGroup V'] [Module F' V']

theorem GlobalTheory.ThetaSpecialise.exists_ratio {fS : S →+* F} {π : S →+* F'} (hf : Function.Injective fS) (mv : N →ₛₗ[fS] V) (mv' : N →ₛₗ[π] V')
    (ind : ∀ (n : ℕ) (c : Fin n → F), (∀ a : Fin n → S, ∑ i, fS (a i) * c i = 0 → ∀ i, a i = 0) →
      ∀ a : Fin n → N, ∑ i, c i • mv (a i) = 0 → ∀ i, a i = 0)
    {I : Type} (a b : I → N) (l : F) (h : ∀ i, mv (a i) = l • mv (b i)) (ha : ∃ i, mv' (a i) ≠ 0)
    (hb : ∃ i, mv' (b i) ≠ 0) : ∃ l' : F', l' ≠ 0 ∧ ∀ i, mv' (a i) = l' • mv' (b i) := by sorry
