-- Prove2me | Theorems.Thm_ModularCurve_exists_hopfAlgebra_torsion_model_jZero_points_hecke_of_relativeGroupLaw
-- name    : ModularCurve.exists_hopfAlgebra_torsion_model_jZero_points_hecke_of_relativeGroupLaw
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/87aa00b0-a34a-511d-ad8f-60a2935132a9
-- title:
--   p-torsion Hopf algebra of a group-law model of J₀(N)
-- statement:
--   Fix $N\ge 1$ and a prime $p$, and write $R=\mathbf Z_{(p)}$ for the subring [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) of $\mathbf Q$ consisting of the rationals whose denominator is coprime to $p$. Let $f\colon J\to\operatorname{Spec}R$ be a scheme over $R$ and let $L$ be a `RelativeGroupLaw` for $f$: multiplication, unit and inversion maps on the sets $\{\varphi\colon T\to J \mid \varphi\circ f=t\}$ of $T$-points over each $t\colon T\to\operatorname{Spec}R$, satisfying associativity, the unit laws, left inverses and naturality under base change, and assumed here commutative for every $T$. Let `pts` be a bijection from $J_0(N)$-divisor classes `JZero N` — the degree-zero part of the divisor class group of the base change to $\overline{\mathbf Q}$ of the modular function field of level $N$ — onto the $\overline{\mathbf Q}$-points of $f$, assumed additive for $L$ and equivariant for $\operatorname{Gal}(\overline{\mathbf Q}/\mathbf Q)$ in the sense that the morphism underlying $\mathrm{pts}(\sigma\cdot x)$ is $\operatorname{Spec}(\sigma)$ followed by that of $\mathrm{pts}(x)$. Let $\varphi^J$ assign to each element $t$ of `HeckeAlg` $=\mathbf Z[X_\ell:\ell\text{ prime}]$ an endomorphism of $J$ over $R$ which is a homomorphism for $L$ on all $T$-points and which computes the action of $t$ on `JZero N` for the module structure `heckeModuleBar N` (evaluation of polynomials at the Hecke operators on $\overline{\mathbf Q}$-classes when these commute, and at zero otherwise): $\mathrm{pts}(t\cdot x)$ is $\mathrm{pts}(x)$ followed by $\varphi^J_t$. Assume finally that `L.schemeNsmul p`, the morphism $J\to J$ underlying the $p$-fold $L$-sum of the identity point, is finite and flat. The conclusion asserts the existence of a commutative ring $H$ carrying a Hopf algebra structure over $R$, finite and flat as an $R$-module and cocommutative, together with: bijections $e_T$, one for every commutative $R$-algebra $T$, from the convolution monoid `WithConv` of $R$-algebra maps $H\to T$ onto the set of $T$-points killed by the $p$-fold $L$-sum; a bijection $e$ from the convolution monoid of $R$-algebra maps $H\to\overline{\mathbf Q}$ onto the $p$-torsion submodule `Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1)`; and a map $\varphi$ from `HeckeAlg` to $R$-algebra endomorphisms of $H$, such that each $e_T$ carries the convolution product to $L$-multiplication; the $e_T$ are natural, in that $e_{T'}(u\circ g)$ has underlying morphism $\operatorname{Spec}(u)$ followed by that of $e_T(g)$ for every $R$-algebra map $u\colon T\to T'$; $\mathrm{pts}(e(g))=e_{\overline{\mathbf Q}}(g)$; $e$ is additive; $e(\sigma\circ g)=\sigma\cdot e(g)$ for $\sigma\in\operatorname{Gal}(\overline{\mathbf Q}/\mathbf Q)$; each $\varphi_t$ maps the kernel of the counit into itself; $e_T(g\circ\varphi_t)$ has underlying morphism that of $e_T(g)$ followed by $\varphi^J_t$; and $e(g\circ\varphi_t)=t\cdot e(g)$.
--
--   This is the passage from a finite flat multiplication-by-$p$ morphism on a group-law model of $J_0(N)$ over $\mathbf Z_{(p)}$ to an affine description of its $p$-torsion: a finite flat cocommutative Hopf algebra over $\mathbf Z_{(p)}$ whose points functor realises $J[p]$, with the dictionary to the $p$-torsion of $J_0(N)(\overline{\mathbf Q})$ compatible with the Galois and Hecke actions. It feeds the cotangent-space computation [`ModularCurve.exists_linearEquiv_baseChange_cotangent_model_jZero_torsion_tensor_intLattice_comp_mapCotangent_eq`](thm.html#ModularCurve.exists_linearEquiv_baseChange_cotangent_model_jZero_torsion_tensor_intLattice_comp_mapCotangent_eq), and its group-law part is supplied by [`GoodReductionJacobian.RelativeGroupLaw.exists_hopfAlgebra_torsion_of_isFinite_of_flat`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_hopfAlgebra_torsion_of_isFinite_of_flat).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_hopfAlgebra_torsion_model_jZero_points_hecke_of_relativeGroupLaw.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve

theorem ModularCurve.exists_hopfAlgebra_torsion_model_jZero_points_hecke_of_relativeGroupLaw
    (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
    {J : Scheme.{0}} {f : J ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))}
    (L : RelativeGroupLaw ↥(GaloisRep.ratLocalizedAt p) f)
    (hcomm : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)))
      (x y : SchemeHomOver t f), L.mul t x y = L.mul t y x)
    (pts : JZero N ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom
      (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))) f)
    (hpts_add : ∀ x y : JZero N, pts (x + y) = L.mul _ (pts x) (pts y))
    (hpts_gal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JZero N),
      (pts (σ • x)).1 =
        Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts x).1)
    (φJ : HeckeAlg → SchemeHomOver f f)
    (hφJ_mul : ∀ (t : HeckeAlg) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)))
      (x y : SchemeHomOver s f),
      NeronModelInfra.schemeHomOverComp (L.mul s x y) (φJ t) =
        L.mul s (NeronModelInfra.schemeHomOverComp x (φJ t))
          (NeronModelInfra.schemeHomOverComp y (φJ t)))
    (hφJ_pts : letI := heckeModuleBar N
      ∀ (t : HeckeAlg) (x : JZero N), (pts (t • x)).1 = (pts x).1 ≫ (φJ t).1)
    (hfin : IsFinite (L.schemeNsmul p)) (hflat : Flat (L.schemeNsmul p)) :
    letI := heckeModuleBar N
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ↥(GaloisRep.ratLocalizedAt p) H),
      Module.Finite ↥(GaloisRep.ratLocalizedAt p) H ∧ Module.Flat ↥(GaloisRep.ratLocalizedAt p) H ∧ Coalgebra.IsCocomm ↥(GaloisRep.ratLocalizedAt p) H ∧
      ∃ (eT : ∀ (T : Type) [CommRing T] [Algebra ↥(GaloisRep.ratLocalizedAt p) T],
          WithConv (H →ₐ[↥(GaloisRep.ratLocalizedAt p)] T) ≃
            L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) T))) p)
        (e : WithConv (H →ₐ[↥(GaloisRep.ratLocalizedAt p)] AlgebraicClosure ℚ) ≃
          ↥(Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1)))
        (φ : HeckeAlg → (H →ₐ[↥(GaloisRep.ratLocalizedAt p)] H)),

        (∀ (T : Type) [CommRing T] [Algebra ↥(GaloisRep.ratLocalizedAt p) T] (g h : WithConv (H →ₐ[↥(GaloisRep.ratLocalizedAt p)] T)),
          ((eT T (g * h)).val : SchemeHomOver _ f) = L.mul _ (eT T g).val (eT T h).val) ∧

        (∀ (T T' : Type) [CommRing T] [Algebra ↥(GaloisRep.ratLocalizedAt p) T] [CommRing T'] [Algebra ↥(GaloisRep.ratLocalizedAt p) T']
            (u : T →ₐ[↥(GaloisRep.ratLocalizedAt p)] T') (g : WithConv (H →ₐ[↥(GaloisRep.ratLocalizedAt p)] T)),
          ((eT T' (.toConv (u.comp g.ofConv))).val : SchemeHomOver _ f).1 =
            Spec.map (CommRingCat.ofHom u.toRingHom) ≫ (eT T g).val.1) ∧

        (∀ g : WithConv (H →ₐ[↥(GaloisRep.ratLocalizedAt p)] AlgebraicClosure ℚ),
          pts (e g : JZero N) = (eT (AlgebraicClosure ℚ) g).val) ∧

        (∀ g h : WithConv (H →ₐ[↥(GaloisRep.ratLocalizedAt p)] AlgebraicClosure ℚ), e (g * h) = e g + e h) ∧

        (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
            (g h : WithConv (H →ₐ[↥(GaloisRep.ratLocalizedAt p)] AlgebraicClosure ℚ)),
          (∀ x : H, h x = σ (g x)) → ((e h : JZero N)) = σ • (e g : JZero N)) ∧

        (∀ t : HeckeAlg,
          RingHom.ker (Bialgebra.counitAlgHom ↥(GaloisRep.ratLocalizedAt p) H) ≤
            (RingHom.ker (Bialgebra.counitAlgHom ↥(GaloisRep.ratLocalizedAt p) H)).comap (φ t)) ∧

        (∀ (t : HeckeAlg) (T : Type) [CommRing T] [Algebra ↥(GaloisRep.ratLocalizedAt p) T] (g : WithConv (H →ₐ[↥(GaloisRep.ratLocalizedAt p)] T)),
          ((eT T (.toConv (g.ofConv.comp (φ t)))).val : SchemeHomOver _ f).1 =
            (eT T g).val.1 ≫ (φJ t).1) ∧

        (∀ (t : HeckeAlg) (g h : WithConv (H →ₐ[↥(GaloisRep.ratLocalizedAt p)] AlgebraicClosure ℚ)),
          (∀ x : H, h x = g (φ t x)) → ((e h : JZero N)) = t • (e g : JZero N)) := by sorry
