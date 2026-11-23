-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_GR_SubGrp_exists_eq_spMap
-- name    : GlobalTheory.CompanionTheory.Ar.GR.SubGrp.exists_eq_spMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:46:54.375641+00:00
-- url     : https://prove2.me/theorems/26f6be81-dc34-4b96-84fd-56d6e071f4af
-- title:
--   Sub Grp: exists eq sp Map
-- statement:
--   The Sub Grp construction uses the exists eq sp Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/FiniteFlatSubgroupScheme.lean#L85-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/FiniteFlatSubgroupScheme.lean#L85-L92

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

theorem GlobalTheory.CompanionTheory.Ar.GR.SubGrp.exists_eq_spMap {S B : Type} [CommRing S] [Algebra R S] [CommRing B] [Algebra R B]
    (x : sp (R₀ := R) S ⟶ sp (R₀ := R) B) : ∃ g : B →ₐ[R] S, x = spMap g := by sorry
