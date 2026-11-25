-- Prove2me | Theorems.Thm_GlobalTheory_WeierstrassCurve_points
-- name    : GlobalTheory.WeierstrassCurve.points
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:49:26.429075+00:00
-- url     : https://prove2.me/theorems/d6ec3035-f4d6-5169-bf42-0445b3b752a1
-- title:
--   Weierstrass Curve: points
-- statement:
--   The Weierstrass Curve construction uses the points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/OverHomEqIffForallIsAlgClosedAlgebra.lean#L482-L523
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/OverHomEqIffForallIsAlgClosedAlgebra.lean#L482-L523

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_OverHomEqIffForallIsAlgClosedAlgebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
universe u
noncomputable section
open GlobalTheory
open GlobalTheory.WeierstrassCurve
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

theorem GlobalTheory.WeierstrassCurve.points :
    (∀ (A : Type u) [CommRing A] [Algebra R A] (P Q : Fin 3 → A)
      (hP : IsUnimodularSol (W.baseChange A) P) (hQ : IsUnimodularSol (W.baseChange A) Q),
      pt W P hP = pt W Q hQ ↔ ∃ v : Aˣ, Q = (v : A) • P) ∧
    (∀ (A : Type u) [CommRing A] [Algebra R A] [IsLocalRing A],
      ∃ e : UnimodularClass (W.baseChange A) ≃
        (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⟶ schemeOver W),
        ∀ P h, (e (Quotient.mk _ ⟨P, h⟩)).left = pt W P h) ∧
    (W.IsElliptic →
      ∃ (e : ∀ (k : Type u) [Field k] [Algebra R k], (W.baseChange k).toAffine.Point ≃
          (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R k))) ⟶ schemeOver W))
        (e' : ∀ (k : Type u) [Field k] [Algebra R k], (W.baseChange k).toProjective.Point ≃
          (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R k))) ⟶ schemeOver W)),
        (∀ (k : Type u) [Field k] [Algebra R k],
          (e k 0).left = Spec.map (CommRingCat.ofHom (algebraMap R k)) ≫ zero W ∧
          (e' k 0).left = Spec.map (CommRingCat.ofHom (algebraMap R k)) ≫ zero W ∧
          (∀ a b h, (e k (.some a b h)).left = pt W ![a, b, 1] (isUnimodularSol_some h.left)) ∧
          (∀ (P : Fin 3 → k)
            (h : (W.baseChange k).toProjective.NonsingularLift (Quotient.mk _ P)),
            (e' k ⟨h⟩).left = pt W P (.of_nonsingular h)) ∧
          (∀ p, e k p.toAffineLift = e' k p)) ∧
        ∀ (k K : Type u) [Field k] [Field K] [Algebra R k] [Algebra R K] [DecidableEq k]
          [DecidableEq K] (f : k →ₐ[R] K),
          (∀ p : (W.baseChange k).toAffine.Point,
            (e K (WeierstrassCurve.Affine.Point.map (W' := W.toAffine) f p)).left =
              Spec.map (CommRingCat.ofHom (f : k →+* K)) ≫ (e k p).left) ∧
          ∀ (P : Fin 3 → k)
            (h : (W.baseChange k).toProjective.NonsingularLift (Quotient.mk _ P))
            (h' : (W.baseChange K).toProjective.NonsingularLift (Quotient.mk _ (f ∘ P))),
            (e' K ⟨h'⟩).left = Spec.map (CommRingCat.ofHom (f : k →+* K)) ≫ (e' k ⟨h⟩).left) ∧
    (∀ (T Y : Over (Spec (.of R))) [IsReduced T.left] [IsSeparated Y.hom] (f g : T ⟶ Y),
      f = g ↔ ∀ (k : Type u) [Field k] (x : Spec (.of k) ⟶ T.left), x ≫ f.left = x ≫ g.left) := by sorry
