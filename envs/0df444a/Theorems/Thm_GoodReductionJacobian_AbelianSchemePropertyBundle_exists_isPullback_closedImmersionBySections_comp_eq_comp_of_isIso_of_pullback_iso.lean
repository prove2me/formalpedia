-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_isPullback_closedImmersionBySections_comp_eq_comp_of_isIso_of_pullback_iso
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_isPullback_closedImmersionBySections_comp_eq_comp_of_isIso_of_pullback_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/bc24cced-b504-5b05-9a99-cb48cf26e308
-- title:
--   Base change of an abelian scheme with polarisation and automorphism
-- statement:
--   Let $\varphi : R \to R'$ be a homomorphism of commutative rings, and let $f : A \to \operatorname{Spec} R$ be a morphism of schemes satisfying `AbelianSchemePropertyBundle R f`, i.e. $f$ is smooth and proper, each fibre $f^{-1}(s)$ is connected, and a relative group law on $f$ exists; let $L$ be such a relative group law, so a functorial group structure on the sets of $T$-points over $\operatorname{Spec} R$. Let $M$ be a module on $A$ that is invertible (locally on $A$ its restriction is isomorphic to the unit module) and satisfies `ClosedImmersionBySections M f`: for some $N$ there is a projective presentation of $M$ relative to $f$ by $N+1$ global sections whose associated morphism $A \to \operatorname{Proj} R[X_0,\dots,X_N]$ is a closed immersion. Let $\sigma$ be an endomorphism of $A$ over $f$ whose underlying morphism is an isomorphism, which is multiplicative in the sense that for all $t : T \to \operatorname{Spec} R$ and all $T$-points $x,y$ over $t$, the point $L.\mathrm{mul}\,t\,x\,y$ followed by $\sigma$ equals $L.\mathrm{mul}\,t$ applied to $x$ followed by $\sigma$ and $y$ followed by $\sigma$; and assume that every point $s$ of $\operatorname{Spec} R$ has an open neighbourhood $U$ such that $\sigma^{*}M$ and $M$ become isomorphic after pullback along the inclusion of $f^{-1}U$. Then all of this data descends along $\varphi$: there exist a scheme $A'$, a morphism $f' : A' \to \operatorname{Spec} R'$ with `AbelianSchemePropertyBundle R' f'`, a relative group law $L'$ on $f'$, an invertible module $M'$ on $A'$ with `ClosedImmersionBySections M' f'`, an endomorphism $\sigma'$ of $A'$ over $f'$ whose underlying morphism is an isomorphism and which is multiplicative for $L'$ in the same sense and satisfies the same local condition $\sigma'^{*}M' \cong M'$ over preimages of a neighbourhood of each point of $\operatorname{Spec} R'$, together with a morphism $p : A' \to A$ making the square formed by $p$, $f'$, $f$ and $\operatorname{Spec}\varphi$ a pullback square, such that: for all $t' : T \to \operatorname{Spec} R'$ and $T$-points $x,y$ of $A'$ over $t'$, the composite of $L'.\mathrm{mul}\,t'\,x\,y$ with $p$ is the underlying morphism of $L.\mathrm{mul}$ at $t'$ followed by $\operatorname{Spec}\varphi$ applied to $x$ followed by $p$ and $y$ followed by $p$; $p^{*}M \cong M'$; and $p \circ \sigma' = \sigma \circ p$.
--
--   This is the base-change compatibility of the package "abelian scheme with a relatively very ample invertible module and an automorphism preserving it up to local isomorphism", in the same shape as the pullback relation between polarised abelian schemes over $R$ and over $R'$. It is used in the study of endomorphisms of polarised abelian schemes, specifically in [`AlgebraicGeometry.PolarisedAbelianScheme.exists_schemeHomOverNpow_eq_schemeHomOverId_of_isIso_of_pullback_pol_iso_of_isAlgClosed`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.exists_schemeHomOverNpow_eq_schemeHomOverId_of_isIso_of_pullback_pol_iso_of_isAlgClosed), where one reduces to a geometric fibre by base change to an algebraically closed field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_isPullback_closedImmersionBySections_comp_eq_comp_of_isIso_of_pullback_iso.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.PolarisedAbelianScheme

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_isPullback_closedImmersionBySections_comp_eq_comp_of_isIso_of_pullback_iso
    {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R')
    {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (hA : AbelianSchemePropertyBundle R f)
    (L : RelativeGroupLaw R f)
    (M : A.Modules) (hM : Scheme.Modules.IsInvertible M) (hci : Scheme.Modules.ClosedImmersionBySections M f)
    (σ : SchemeHomOver f f) (hσiso : IsIso σ.1)
    (hσ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) σ =
        L.mul t (NeronModelInfra.schemeHomOverComp x σ) (NeronModelInfra.schemeHomOverComp y σ))
    (hpol : ∀ s : ↥(Spec (CommRingCat.of R)), ∃ U : (Spec (CommRingCat.of R)).Opens, s ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback σ.1).obj M) ≅
        (Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj M)) :
    ∃ (A' : Scheme.{0}) (f' : A' ⟶ Spec (CommRingCat.of R')) (L' : RelativeGroupLaw R' f')
      (_ : AbelianSchemePropertyBundle R' f')
      (M' : A'.Modules) (_ : Scheme.Modules.IsInvertible M') (_ : Scheme.Modules.ClosedImmersionBySections M' f')
      (σ' : SchemeHomOver f' f') (_ : IsIso σ'.1)
      (_ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R')) (x y : SchemeHomOver t f'),
        NeronModelInfra.schemeHomOverComp (L'.mul t x y) σ' =
          L'.mul t (NeronModelInfra.schemeHomOverComp x σ') (NeronModelInfra.schemeHomOverComp y σ'))
      (_ : ∀ s : ↥(Spec (CommRingCat.of R')), ∃ U : (Spec (CommRingCat.of R')).Opens, s ∈ U ∧
        Nonempty ((Scheme.Modules.pullback (f' ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback σ'.1).obj M') ≅
          (Scheme.Modules.pullback (f' ⁻¹ᵁ U).ι).obj M'))
      (p : A' ⟶ A) (hp : CategoryTheory.IsPullback p f' f (Spec.map (CommRingCat.ofHom φ))),
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of R')) (x y : SchemeHomOver t' f'),
        (L'.mul t' x y).1 ≫ p =
          (L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
            ⟨x.1 ≫ p, by rw [Category.assoc, hp.w, ← Category.assoc, x.2]⟩
            ⟨y.1 ≫ p, by rw [Category.assoc, hp.w, ← Category.assoc, y.2]⟩).1) ∧
      Nonempty ((Scheme.Modules.pullback p).obj M ≅ M') ∧
      σ'.1 ≫ p = p ≫ σ.1 := by sorry
