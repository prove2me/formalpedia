-- Prove2me | Theorems.Thm_GlobalTheory_InvExt_exists_common_residue
-- name    : GlobalTheory.InvExt.exists_common_residue
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:14:40.71198+00:00
-- url     : https://prove2.me/theorems/6f0e74ed-a9a8-46af-8691-47238d6476a1
-- title:
--   Inv Ext: exists common residue
-- statement:
--   The Inv Ext construction uses the exists common residue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsInverseExtensionProperClosure.lean#L96-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsInverseExtensionProperClosure.lean#L96-L103

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteOfIsClosedOfFiniteInterClosedPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsInverseExtensionProperClosure
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
open GlobalTheory GlobalTheory.InvExt
variable (C : Core)
variable {C}

theorem GlobalTheory.InvExt.exists_common_residue {X : Scheme.{0}} {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (α : Sp (OO p) ⟶ X) (β : Sp (OO q) ⟶ X) (h : α (cPt p) = β (cPt q)) :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (v : Sp K ⟶ Sp (kb p)) (v' : Sp K ⟶ Sp (kb q)),
      v ≫ rPt p ≫ α = v' ≫ rPt q ≫ β := by sorry
