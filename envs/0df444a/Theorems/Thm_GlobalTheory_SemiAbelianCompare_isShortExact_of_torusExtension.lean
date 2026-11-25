-- Prove2me | Theorems.Thm_GlobalTheory_SemiAbelianCompare_isShortExact_of_torusExtension
-- name    : GlobalTheory.SemiAbelianCompare.isShortExact_of_torusExtension
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:39:48.045807+00:00
-- url     : https://prove2.me/theorems/4601275f-91c0-41ef-8fe5-288875eea09b
-- title:
--   Semi Abelian Compare: is Short Exact of torus Extension
-- statement:
--   The Semi Abelian Compare construction uses the is Short Exact of torus Extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/QuasiCompactIffLocallyOfFinitePresentation.lean#L138-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/QuasiCompactIffLocallyOfFinitePresentation.lean#L138-L147

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
variable {k : Type u} [Field k] {G : Over (Spec (CommRingCat.of k))} [GrpObj G]

theorem GlobalTheory.SemiAbelianCompare.isShortExact_of_torusExtension (E : Semi.TorusExtension G) :
    letI := E.addCommGroup; letI := E.grpB
    IndefiniteRowSideFullHecke.SemiAbelianSchemes.IsAbelianScheme E.B ∧ IndefiniteRowSideFullHecke.SemiAbelianSchemes.IsShortExact E.i E.q := by sorry
