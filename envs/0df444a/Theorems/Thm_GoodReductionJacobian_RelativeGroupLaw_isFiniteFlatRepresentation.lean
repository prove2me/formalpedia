-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFiniteFlatRepresentation
-- name    : GoodReductionJacobian.RelativeGroupLaw.isFiniteFlatRepresentation
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:05:45.010267+00:00
-- url     : https://prove2.me/theorems/0005d1d0-b74d-419e-b5e1-ae64cc3887aa
-- title:
--   A finite flat commutative group scheme realizes a finite-flat local representation
-- statement:
--   Let $p$ be prime, let $W$ be an abelian group with an action of $G_ℚ$, and let $X$ be a finite flat scheme over $ℚ$ localized at $p$, equipped with a commutative relative group law. Assume an equivalence $e:W≃X(\overline{ℚ})$ carries addition to the group law and intertwines the global Galois action with the action on geometric points. Then the restricted local action is finite flat: $$σ↦\bigl(x↦\operatorname{act}(\operatorname{locToGlob}_p(σ),x)\bigr)\text{ is a finite-flat representation at }p.$$ Formalization note: the chosen local-to-global embedding and the point equivalence are explicit bookkeeping data.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj
import Theorems.Thm_AlgebraicGeometry_exists_hopfAlgebra_flat_of_grpObj_over_spec
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_GroupCohomology_FiniteFlatCocycle

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry NeronModelInfra
open scoped CategoryTheory.MonObj
open GoodReductionJacobian
open GoodReductionJacobian.RelativeGroupLaw

theorem GoodReductionJacobian.RelativeGroupLaw.isFiniteFlatRepresentation
    (p : ℕ) [Fact p.Prime]
    {W : Type} [AddCommGroup W]
    (act : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → W → W)
    {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of (GaloisRep.ratLocalizedAt p)))
    [IsFinite f] [Flat f]
    (L : GoodReductionJacobian.RelativeGroupLaw (GaloisRep.ratLocalizedAt p) f)
    (hc : L.IsCommutative)
    (e : W ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom
      (algebraMap (GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))) f)
    (he_add : ∀ x y, e (x + y) = L.mul _ (e x) (e y))
    (he_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : W),
      (e (act σ x)).1 = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (e x).1) :
    groupCohomology.IsFiniteFlatRepresentation p
      (fun σ => act (localGaloisToGlobal p σ)) := by sorry
