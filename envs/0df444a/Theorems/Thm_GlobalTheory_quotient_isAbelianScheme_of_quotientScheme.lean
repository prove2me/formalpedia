-- Prove2me | Theorems.Thm_GlobalTheory_quotient_isAbelianScheme_of_quotientScheme
-- name    : GlobalTheory.quotient_isAbelianScheme_of_quotientScheme
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:50:04.055477+00:00
-- url     : https://prove2.me/theorems/11996298-ef6e-5982-beb1-b1d897f34810
-- title:
--   Global Theory: quotient is Abelian Scheme of quotient Scheme
-- statement:
--   The Global Theory construction uses the quotient is Abelian Scheme of quotient Scheme property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/QuotientIsAbelianSchemeOfQuotientScheme.lean#L189-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/QuotientIsAbelianSchemeOfQuotientScheme.lean#L189-L217

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatQuotientIsoOfSameKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FormallyUnramifiedOfCompOfEtaleOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_QuotientIsAbelianSchemeOfQuotientScheme
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open AbelianQuotient

theorem GlobalTheory.quotient_isAbelianScheme_of_quotientScheme :
    (∀ (X S : Scheme.{0}) (f : X ⟶ S), Smooth f → GeometricallyConnected f →
      GeometricallyIntegral f) →
    (∀ (R : Type) [CommRing R] [IsNoetherianRing R] (P : PolAV (Spec (CommRingCat.of R)))
      (H : Over (Spec (CommRingCat.of R))) [GrpObj H] (i : H ⟶ P.A), IsMonHom i → Mono i →
      IsFinite H.hom → Flat H.hom →
      ∃ (Q : Over (Spec (CommRingCat.of R))) (q : P.A ⟶ Q), IsFinite q.left ∧ Flat q.left ∧
        Surjective q.left ∧ IsSeparated Q.hom ∧ LocallyOfFiniteType Q.hom ∧
        IsPullback ((fst H P.A ≫ i) * snd H P.A) (snd H P.A) q q) →
    QuotientSt := by sorry
