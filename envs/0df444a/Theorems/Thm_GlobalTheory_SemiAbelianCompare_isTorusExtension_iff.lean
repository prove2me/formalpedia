-- Prove2me | Theorems.Thm_GlobalTheory_SemiAbelianCompare_isTorusExtension_iff
-- name    : GlobalTheory.SemiAbelianCompare.isTorusExtension_iff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:51:16.675302+00:00
-- url     : https://prove2.me/theorems/bb38a9c8-5bf4-5980-bf57-15ee901da83e
-- title:
--   Semi Abelian Compare: is Torus Extension iff
-- statement:
--   The Semi Abelian Compare construction uses the is Torus Extension iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/QuasiCompactIffLocallyOfFinitePresentation.lean#L172-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/QuasiCompactIffLocallyOfFinitePresentation.lean#L172-L177

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
variable (G)

theorem GlobalTheory.SemiAbelianCompare.isTorusExtension_iff :
    IsCommMonObj G ∧ Nonempty (Semi.TorusExtension G) ↔ IndefiniteRowSideFullHecke.SemiAbelianSchemes.IsTorusExtension G := by sorry
