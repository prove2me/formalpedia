-- Prove2me | Theorems.Thm_GlobalTheory_AdmLoc_Ea_apply
-- name    : GlobalTheory.AdmLoc.Ea_apply
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:09:25.352018+00:00
-- url     : https://prove2.me/theorems/6ffe8fda-7659-40f4-94b4-248bd4e052ad
-- title:
--   Adm Loc: Ea apply
-- statement:
--   The Adm Loc construction uses the Ea apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MkMemAdmissibleAtIffCocycle.lean#L318-L322
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MkMemAdmissibleAtIffCocycle.lean#L318-L322

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

theorem GlobalTheory.AdmLoc.Ea_apply (z : ↥(Z1 (twCoef W χ X) ⊤)) (g : G) (m : M ⊗[O] X) (y : O) :
    Ea W χ hc z g (m, Ideal.Quotient.mk _ y) =
      (coefRep W X g m + ((χ g : O) * y) • (z : G → M ⊗[O] X) g, Ideal.Quotient.mk _ ((χ g : O) * y)) := by sorry
