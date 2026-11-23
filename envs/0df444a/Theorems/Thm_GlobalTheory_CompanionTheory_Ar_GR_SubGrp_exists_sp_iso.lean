-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_GR_SubGrp_exists_sp_iso
-- name    : GlobalTheory.CompanionTheory.Ar.GR.SubGrp.exists_sp_iso
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:46:21.182588+00:00
-- url     : https://prove2.me/theorems/c3dde482-dd60-44bd-b814-18e9e04b9da1
-- title:
--   Sub Grp: exists sp iso
-- statement:
--   The Sub Grp construction uses the exists sp iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/FiniteFlatSubgroupScheme.lean#L94-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/FiniteFlatSubgroupScheme.lean#L94-L105

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_CommutativeAlgebra_IsFinFlatSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteFlatSubgroupScheme
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.GR GlobalTheory.CompanionTheory.Ar.GR.SubGrp
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.GR
variable {R : Type} [CommRing R]

theorem GlobalTheory.CompanionTheory.Ar.GR.SubGrp.exists_sp_iso (T : Over (Spec (CommRingCat.of R))) [IsAffine T.left] :
    ∃ (S : Type) (_ : CommRing S) (_ : Algebra R S) (j : sp (R₀ := R) S ⟶ T), IsIso j := by sorry
