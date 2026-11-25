-- Prove2me | Theorems.Thm_GlobalTheory_Compare_AbelianSchemeTorusCompare_isAbelianScheme_of_iso
-- name    : GlobalTheory.Compare.AbelianSchemeTorusCompare.isAbelianScheme_of_iso
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:02:32.69071+00:00
-- url     : https://prove2.me/theorems/1bd56735-241b-414d-9b21-7e208eacd725
-- title:
--   Abelian Scheme Torus Compare: is Abelian Scheme of iso
-- statement:
--   The Abelian Scheme Torus Compare construction uses the is Abelian Scheme of iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/AbelianSchemeTorusCompare.lean#L29-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/AbelianSchemeTorusCompare.lean#L29-L47

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_GenericFiberGluing_SemistableCompleteSplit
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_SemiAbelianModels
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_AbelianSchemeTorusCompare
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
open ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory GlobalTheory.Compare GlobalTheory.Compare.AbelianSchemeTorusCompare
open GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianModels

theorem GlobalTheory.Compare.AbelianSchemeTorusCompare.isAbelianScheme_of_iso {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B]
    (e : A ≅ B) (he : IsMonHom e.hom) (hB : IsAbelianScheme B) : IsAbelianScheme A := by sorry
