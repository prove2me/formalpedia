-- Prove2me | Theorems.Thm_GlobalTheory_SemiAbelianCompare_nonempty_torusExtension_iff
-- name    : GlobalTheory.SemiAbelianCompare.nonempty_torusExtension_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T15:39:00.786936+00:00
-- url     : https://prove2.me/theorems/5f23961b-1135-4e5f-8436-b11983c85a32
-- title:
--   Semi Abelian Compare: nonempty torus Extension iff
-- statement:
--   The Semi Abelian Compare construction uses the nonempty torus Extension iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/QuasiCompactIffLocallyOfFinitePresentation.lean#L205-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/QuasiCompactIffLocallyOfFinitePresentation.lean#L205-L208

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_SemiAbelianSchemes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsTorusAndQuotientHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_QuasiCompactIffLocallyOfFinitePresentation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G
open GlobalTheory GlobalTheory.SemiAbelianCompare

theorem GlobalTheory.SemiAbelianCompare.nonempty_torusExtension_iff {k : Type} [Field k] (G : Over (Spec (CommRingCat.of k)))
    [GrpObj G] : Nonempty (Semi.TorusExtension G) ↔ IndefiniteRowSideFullHecke.SemiAbelianSchemes.IsTorusExtension G := by sorry
