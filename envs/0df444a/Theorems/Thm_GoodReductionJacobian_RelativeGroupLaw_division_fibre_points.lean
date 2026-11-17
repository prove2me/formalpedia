-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_division_fibre_points
-- name    : GoodReductionJacobian.RelativeGroupLaw.division_fibre_points
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:05:32.079799+00:00
-- url     : https://prove2.me/theorems/e1e94372-cdbe-4c61-8ceb-505167b8077e
-- title:
--   Points of the division-carry scheme are indexed by residue classes and division equations
-- statement:
--   Let $L$ be a relative group law on $B/R$, let $S$ be a section, and let $T=\operatorname{Spec}K$ for a local ring $K$. Suppose an additive group $W$ is identified with $B(T)$ by an equivalence $e$ preserving addition, and let $P∈W$ correspond to $S_T$. For $X_a=[71]^{-1}([a]S)$ and $X=\coprod_aX_a$, there is an equivalence $$\coprod_{a∈ℤ/71ℤ}\{x∈W:71x=a_{val}P\}\;≃\;X(T).$$ Under this equivalence, a pair $(a,x)$ is represented by the pullback lift in $X_a$ and projects back to $e(x)$. This identifies the geometric points of the finite-flat Kummer model.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_coe_nsmul_eq_comp_schemeNsmul
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open GoodReductionJacobian
open GoodReductionJacobian.RelativeGroupLaw

theorem GoodReductionJacobian.RelativeGroupLaw.division_fibre_points
    {R : Type} [CommRing R] {B : Scheme.{0}}
    {f : B ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f)
    (S : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    {K : Type} [CommRing K] [IsLocalRing K]
    (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
    {W : Type} [AddCommGroup W]
    (e : W ≃ SchemeHomOver t f)
    (he_add : ∀ x y, e (x + y) = L.mul t (e x) (e y))
    (P : W) (hP : e P = GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) S) :
    let X : ZMod 71 → Scheme.{0} := fun a =>
      pullback (L.schemeNsmul 71) (L.nsmul (𝟙 _) a.val S).1
    let g : ∀ a, X a ⟶ Spec (CommRingCat.of R) := fun a =>
      pullback.snd (L.schemeNsmul 71) (L.nsmul (𝟙 _) a.val S).1
    ∃ E : (Σ a : ZMod 71, {x : W // 71 • x = a.val • P}) ≃
        SchemeHomOver t (Sigma.desc g),
      ∀ x, ∃ h : (e x.2.1).1 ≫ L.schemeNsmul 71 =
          t ≫ (L.nsmul (𝟙 _) x.1.val S).1,
        (E x).1 = pullback.lift (e x.2.1).1 t h ≫ Sigma.ι X x.1 ∧
        ∃ z : SchemeHomOver t (g x.1),
          z.1 ≫ Sigma.ι X x.1 = (E x).1 ∧
          z.1 ≫ pullback.fst (L.schemeNsmul 71)
            (L.nsmul (𝟙 _) x.1.val S).1 = (e x.2.1).1 := by sorry
