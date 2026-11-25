-- Prove2me | Theorems.Thm_GlobalTheory_GrpTangent_etale_hom_and_mulN
-- name    : GlobalTheory.GrpTangent.etale_hom_and_mulN
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:06:23.663142+00:00
-- url     : https://prove2.me/theorems/cf51a08e-308b-4ff8-a29d-78e6da9172f0
-- title:
--   Grp Tangent: etale hom and mul N
-- statement:
--   The Grp Tangent construction uses the etale hom and mul N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedOfTangentMapInjective.lean#L669-L692
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FormallyUnramifiedOfTangentMapInjective.lean#L669-L692

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.GrpTangent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR epsScaleR IsTangent)
open ReciprocityTheory.ChartRestriction.G.Semi (mulN torsion IsAbelianScheme)
open scoped CategoryTheory.Obj
open TangentCrit

theorem GlobalTheory.GrpTangent.etale_hom_and_mulN :
    (∀ (S : Scheme.{0}) (G H : Over S) [GrpObj G] [GrpObj H] [Smooth G.hom] [Smooth H.hom]
      (f : G ⟶ H) [IsMonHom f],
      ((∀ (k : Type) [Field k] [IsAlgClosed k] (p : Sp k ⟶ S),
        Function.Bijective (tangentMap ((Over.pullback p).map f))) → Etale f.left) ∧
      ((∀ (k : Type) [Field k] [IsAlgClosed k] (p : Sp k ⟶ S),
        Function.Injective (tangentMap ((Over.pullback p).map f))) → FormallyUnramified f.left) ∧
      ((∀ (k : Type) [Field k] [IsAlgClosed k] (p : Sp k ⟶ S),
        Function.Surjective (tangentMap ((Over.pullback p).map f))) → Smooth f.left)) ∧
    (∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (n : ℕ) (w : epsR R ⟶ G),
      IsTangent w → (w ≫ mulN G n).left = spMap (epsScaleR (n : R)) ≫ w.left) ∧
    (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (n : ℕ),
      IsUnit (n : Γ(S, ⊤)) → Etale (mulN G n).left ∧ Etale (torsion G n).hom) ∧
    (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsAbelianScheme G] (n : ℕ),
      IsUnit (n : Γ(S, ⊤)) → (IsFinite (mulN G n).left ∧ Etale (mulN G n).left) ∧
        IsFinite (torsion G n).hom ∧ Etale (torsion G n).hom) := by sorry
