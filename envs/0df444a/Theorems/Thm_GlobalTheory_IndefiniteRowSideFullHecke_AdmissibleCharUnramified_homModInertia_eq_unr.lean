-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_AdmissibleCharUnramified_homModInertia_eq_unr
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleCharUnramified.homModInertia_eq_unr
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:09:07.236488+00:00
-- url     : https://prove2.me/theorems/f379d6ff-bb6e-4ae4-9b7a-c6718d3e32e0
-- title:
--   Admissible Char Unramified: hom Mod Inertia eq unr
-- statement:
--   The Admissible Char Unramified construction uses the hom Mod Inertia eq unr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/AdmissibleCharUnramified.lean#L37-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/AdmissibleCharUnramified.lean#L37-L46

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MkMemAdmissibleAtIffCocycle
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_AdmissibleCharUnramified
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleCharUnramified
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions TensorProduct GlobalTheory.AdmLoc
open ReciprocityTheory.Def (Z1 H1)
variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] (Γ : GalData G Qp LL O)
    (X : Type) [AddCommGroup X] [Module O X]

theorem GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleCharUnramified.homModInertia_eq_unr (I : Subgroup G) :
    homModInertia Γ X I = (unr (twCoef (Γ.Wchi 1) Γ.χ₁ X) I : Set _) := by sorry
