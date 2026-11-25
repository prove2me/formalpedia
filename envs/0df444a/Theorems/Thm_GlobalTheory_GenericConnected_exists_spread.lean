-- Prove2me | Theorems.Thm_GlobalTheory_GenericConnected_exists_spread
-- name    : GlobalTheory.GenericConnected.exists_spread
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:53:57.57158+00:00
-- url     : https://prove2.me/theorems/a7fec4a2-5cad-4f46-bdf0-587c8a48b49a
-- title:
--   Generic Connected: exists spread
-- statement:
--   The Generic Connected construction uses the exists spread property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/GeometricallyConnectedGenericFibreOfDense.lean#L13-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/GeometricallyConnectedGenericFibreOfDense.lean#L13-L145

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsIsAffineOpenDisjointImageOfIsConstructible
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GeometricallyConnectedGenericFibreOfDense
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
local notation "OO" p:max => (Valuation.valuationSubring (Valued.v : Valuation (PadicAlgCl p) NNReal))
local notation "cPt" p:max => (IsLocalRing.closedPoint (OO p) : Sp (OO p))
local notation "gPt" p:max => spMap (ValuationSubring.subtype (OO p))
open GlobalTheory GlobalTheory.GenericConnected

theorem GlobalTheory.GenericConnected.exists_spread {X Y S : Scheme.{0}} {R A : Type} [CommRing R] [CommRing A]
    [IsNoetherianRing R] [Algebra R A] (j : Spec (.of R) ⟶ S) {p : X ⟶ S} [QuasiCompact p]
    [LocallyOfFiniteType p] {g : Y ⟶ X} {q : Y ⟶ Spec (.of A)}
    (H : IsPullback g q p (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ j))
    (U V : Y.Opens) (hsup : U ⊔ V = ⊤) (hinf : U ⊓ V = ⊥) :
    ∃ (T : Scheme.{0}) (a : T ⟶ Spec (.of R)) (_ : LocallyOfFiniteType a) (_ : IsAffine T)
      (b : Spec (.of A) ⟶ T) (π : Y ⟶ pullback p (a ≫ j)) (U' V' : (pullback p (a ≫ j)).Opens),
      b ≫ a = Spec.map (CommRingCat.ofHom (algebraMap R A)) ∧
      π ≫ pullback.snd p (a ≫ j) = q ≫ b ∧
      U' ⊔ V' = ⊤ ∧ U' ⊓ V' = ⊥ ∧ π ⁻¹ᵁ U' = U ∧ π ⁻¹ᵁ V' = V := by sorry
