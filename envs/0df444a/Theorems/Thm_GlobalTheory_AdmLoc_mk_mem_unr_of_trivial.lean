-- Prove2me | Theorems.Thm_GlobalTheory_AdmLoc_mk_mem_unr_of_trivial
-- name    : GlobalTheory.AdmLoc.mk_mem_unr_of_trivial
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:10:20.504815+00:00
-- url     : https://prove2.me/theorems/e682b1f9-ff94-48eb-96ae-3594b2696d05
-- title:
--   Adm Loc: mk mem unr of trivial
-- statement:
--   The Adm Loc construction uses the mk mem unr of trivial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MkMemAdmissibleAtIffCocycle.lean#L401-L410
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MkMemAdmissibleAtIffCocycle.lean#L401-L410

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_QuotientHomNonvanishingBound
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_StatementTor
import Definitions.Def_ReciprocityTheory_BasicDefinitions_AdRep
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesOneAddConstMulXMulInv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MkMemAdmissibleAtIffCocycle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.AdmLoc
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions TensorProduct
open Formalism.MainNotions.N (twistRep coefRep)
open Formalism.GaloisCohomology (scalRep)
open ReciprocityTheory.Def (Z1 B1 H1 d0 d1 C1)
open scoped Pointwise
variable {O G : Type} [CommRing O] [Group G]
variable {M M' : Type} [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M']
variable [TopologicalSpace G]

theorem GlobalTheory.AdmLoc.mk_mem_unr_of_trivial {π : Representation O G M} (hπ : ∀ g m, π g m = m) (I : Subgroup G)
    (z : ↥(Z1 π ⊤)) : (Submodule.Quotient.mk z : H1 π ⊤) ∈ unr π I ↔ ∀ g ∈ I, (z : G → M) g = 0 := by sorry
