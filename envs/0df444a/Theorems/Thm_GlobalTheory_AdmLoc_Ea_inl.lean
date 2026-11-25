-- Prove2me | Theorems.Thm_GlobalTheory_AdmLoc_Ea_inl
-- name    : GlobalTheory.AdmLoc.Ea_inl
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:57:07.178365+00:00
-- url     : https://prove2.me/theorems/d779930f-f10c-43b7-b4b6-67ed613092a3
-- title:
--   Adm Loc: Ea inl
-- statement:
--   The Adm Loc construction uses the Ea inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MkMemAdmissibleAtIffCocycle.lean#L324-L327
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MkMemAdmissibleAtIffCocycle.lean#L324-L327

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
variable (W : Representation O G M) (χ : G →* Oˣ) {X : Type} [AddCommGroup X] [Module O X] {c : O}
    (hc : ∀ x : X, c • x = 0)

theorem GlobalTheory.AdmLoc.Ea_inl (z : ↥(Z1 (twCoef W χ X) ⊤)) (g : G) (m : M ⊗[O] X) :
    Ea W χ hc z g (m, 0) = (coefRep W X g m, 0) := by sorry
