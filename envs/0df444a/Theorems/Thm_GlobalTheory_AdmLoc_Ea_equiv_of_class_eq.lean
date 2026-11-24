-- Prove2me | Theorems.Thm_GlobalTheory_AdmLoc_Ea_equiv_of_class_eq
-- name    : GlobalTheory.AdmLoc.Ea_equiv_of_class_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T19:13:24.440338+00:00
-- url     : https://prove2.me/theorems/6b85069d-baf4-4be8-96e5-7954e126391d
-- title:
--   Adm Loc: Ea equiv of class eq
-- statement:
--   The Adm Loc construction uses the Ea equiv of class eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MkMemAdmissibleAtIffCocycle.lean#L339-L358
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MkMemAdmissibleAtIffCocycle.lean#L339-L358

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

theorem GlobalTheory.AdmLoc.Ea_equiv_of_class_eq {z z' : ↥(Z1 (twCoef W χ X) ⊤)}
    (h : (Submodule.Quotient.mk z : H1 (twCoef W χ X) ⊤) = Submodule.Quotient.mk z') :
    ∃ e : ((M ⊗[O] X) × (O ⧸ Ideal.span {c})) ≃ₗ[O] ((M ⊗[O] X) × (O ⧸ Ideal.span {c})),
      (∀ g x, e (Ea W χ hc z g x) = Ea W χ hc z' g (e x)) ∧ (∀ m, e (m, 0) = (m, 0)) ∧ ∀ x, (e x).2 = x.2 := by sorry
