-- Prove2me | Theorems.Thm_GlobalTheory_SemiAbelianCompare_isSemiAbelian_iff
-- name    : GlobalTheory.SemiAbelianCompare.isSemiAbelian_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:39:49.458952+00:00
-- url     : https://prove2.me/theorems/b60b8095-fe7e-48e0-8e82-bd8ea853221c
-- title:
--   Semi Abelian Compare: is Semi Abelian iff
-- statement:
--   The Semi Abelian Compare construction uses the is Semi Abelian iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/QuasiCompactIffLocallyOfFinitePresentation.lean#L210-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/QuasiCompactIffLocallyOfFinitePresentation.lean#L210-L225

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

theorem GlobalTheory.SemiAbelianCompare.isSemiAbelian_iff {S : Scheme.{u}} (G : Over S) [GrpObj G] :
    Semi.IsSemiAbelian G ↔ IndefiniteRowSideFullHecke.SemiAbelianSchemes.IsSemiAbelianScheme G := by sorry
