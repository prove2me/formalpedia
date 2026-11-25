-- Prove2me | Theorems.Thm_GlobalTheory_semiAbelian_notions_equiv
-- name    : GlobalTheory.semiAbelian_notions_equiv
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T15:43:26.774588+00:00
-- url     : https://prove2.me/theorems/fdeb8f44-edde-42c4-a7ed-17eeef2515e9
-- title:
--   Global Theory: semi Abelian notions equiv
-- statement:
--   The Global Theory construction uses the semi Abelian notions equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/QuasiCompactIffLocallyOfFinitePresentation.lean#L233-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/QuasiCompactIffLocallyOfFinitePresentation.lean#L233-L256

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
open GlobalTheory
open SemiAbelianCompare

theorem GlobalTheory.semiAbelian_notions_equiv :
    (∀ (S : Scheme.{u}) (A : Over S) [GrpObj A],
      Semi.IsAbelianScheme A ↔ IndefiniteRowSideFullHecke.SemiAbelianSchemes.IsAbelianScheme A) ∧
    (∀ (k : Type u) [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G]
      (X : Type u) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
      (B : Over (Spec (CommRingCat.of k))) [GrpObj B]
      (i : Semi.splitTorus (Spec (CommRingCat.of k)) X ⟶ G) (q : G ⟶ B),
      (Semi.IsAbelianScheme B ∧ IsMonHom q ∧ Flat q.left ∧ Surjective q.left ∧
          QuasiCompact q.left ∧ IsMonHom i ∧ IsPullback i (toUnit _) q (η : 𝟙_ _ ⟶ B)) ↔
        (IndefiniteRowSideFullHecke.SemiAbelianSchemes.IsAbelianScheme B ∧ IndefiniteRowSideFullHecke.SemiAbelianSchemes.IsShortExact i q)) ∧
    (∀ (k : Type u) [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G],
      IsCommMonObj G ∧ Nonempty (Semi.TorusExtension G) ↔ IndefiniteRowSideFullHecke.SemiAbelianSchemes.IsTorusExtension G) ∧
    (∀ (k : Type) [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G],
      Nonempty (Semi.TorusExtension G) ↔ IndefiniteRowSideFullHecke.SemiAbelianSchemes.IsTorusExtension G) ∧
    (∀ (S : Scheme.{u}) (G : Over S) [GrpObj G],
      Semi.IsSemiAbelian G ↔ IndefiniteRowSideFullHecke.SemiAbelianSchemes.IsSemiAbelianScheme G) := by sorry
