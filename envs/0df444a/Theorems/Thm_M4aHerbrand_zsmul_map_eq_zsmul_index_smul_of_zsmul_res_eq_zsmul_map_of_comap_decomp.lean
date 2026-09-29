-- Prove2me | Theorems.Thm_M4aHerbrand_zsmul_map_eq_zsmul_index_smul_of_zsmul_res_eq_zsmul_map_of_comap_decomp
-- name    : M4aHerbrand.zsmul_map_eq_zsmul_index_smul_of_zsmul_res_eq_zsmul_map_of_comap_decomp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/dc10e26f-d682-5c6f-89c0-91671ebc41a1
-- title:
--   Semilocal degree-two class equals index times a restricting class
-- statement:
--   Let $E\subseteq F\subseteq F'$ be number fields forming a scalar tower with $F/E$ and $F'/E$ Galois. Let $D'$ be an idèle Galois descent datum for $F'/E$, i.e. a homomorphism from $F'\simeq_E F'$ to the ring automorphisms of $\mathrm{AdeleRing}(\mathcal O_{F'},F')$ that is continuous and compatible with $F'\to\mathrm{AdeleRing}$, together with a multiplicative-distributive action of $F'\simeq_E F'$ on the idèle class group $C_{F'}=(\mathrm{AdeleRing})^\times/\text{principal idèles}$ which, by `hact'`, coincides with the induced action `D'.classAct`. Let $\iota'$ (for $F'$) and $\iota$ (for $F$) assign to each finite place and each unit $x$ of its completion an idèle whose component at that place is $x$, whose other finite components and whose infinite part are $1$. Fix a finite place $W$ of $F'$, write $w=W\cap\mathcal O_F$, let $D'_W=\mathrm{decomp}\,E\,F'\,W$ and $D_w=\mathrm{decomp}\,E\,F\,w$ be the decomposition subgroups of the respective valuation subrings, and let $H$ be the preimage of $D_w$ under restriction $\mathrm{Gal}(F'/E)\to\mathrm{Gal}(F/E)$; `hle` says $D'_W\le H$. Given a homomorphism $r\colon D'_W\to D_w$ compatible with restriction along $F\to F'$ (`hr`), a morphism of representations $i_W$ over $r$ realised by the base-change map $F_w\to F'_W$ of adic completions (`hiW`), a morphism $\kappa$ over $H\to D_w$ sending $x\in F_w^\times$ to the class of the base-changed idèle $\beta(\iota_w x)$ (`hκ`), and a $D'_W$-morphism $\varphi_W$ sending $x\in F'^\times_W$ to the class of $\iota'_W x$ (`hφW`): for all $k\in\mathbb Z$, $z\in H^2(D_w,F_w^\times)$ and $y\in H^2(H,C_{F'})$, if $k$ times the restriction of $y$ to $D'_W$ equals $k$ times $\varphi_{W,*}(H^2(r,i_W)(z))$, then $k\cdot H^2(H\to D_w,\kappa)(z)=k\cdot[H:D'_W]\cdot y$, the index being that of $D'_W$ inside $H$, coerced to $\mathbb Z$.
--
--   This is a corestriction-free formulation of the Shapiro-lemma identity for the semilocal component above $w$: the idèles of $F'$ supported above $w$ form the module coinduced from $F'^\times_W$ along $D'_W\le H$, so pushing a degree-two class of $D_w$ forward to $C_{F'}$ agrees with $[H:D'_W]$ times any class of $H$ whose restriction to $D'_W$ is the local reading at $W$. It feeds the construction of a fundamental class for the idèle class group in [`M4aHerbrand.exists_fundamentalClass_ideleClassGroup_map_eq_finrank_smul_of_ne_two`](thm.html#M4aHerbrand.exists_fundamentalClass_ideleClassGroup_map_eq_finrank_smul_of_ne_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_zsmul_map_eq_zsmul_index_smul_of_zsmul_res_eq_zsmul_map_of_comap_decomp.lean

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_M4aHerbrand_GenuineBeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
open CategoryTheory NumberField IsDedekindDomain M4aHerbrand
open scoped NumberField.PlaceDecomp

theorem M4aHerbrand.zsmul_map_eq_zsmul_index_smul_of_zsmul_res_eq_zsmul_map_of_comap_decomp
    (E F F' : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field F'] [NumberField F']
    [Algebra E F] [Algebra E F'] [Algebra F F'] [IsScalarTower E F F'] [IsGalois E F] [IsGalois E F']

    (D' : IdeleGaloisDescent (𝓞 F') E F')
    [MulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')]
    (hact' : ∀ (g : F' ≃ₐ[E] F') (c : IdeleClassGroup (𝓞 F') F'), g • c = D'.classAct g c)
    (ι' : ∀ w : HeightOneSpectrum (𝓞 F'), (w.adicCompletion F')ˣ →* (AdeleRing (𝓞 F') F')ˣ)
    (hι' : ∀ (w : HeightOneSpectrum (𝓞 F')) (x : (w.adicCompletion F')ˣ),
      finPart w (ι' w x) = x ∧ (∀ w' : HeightOneSpectrum (𝓞 F'), w' ≠ w → finPart w' (ι' w x) = 1) ∧ infPart (ι' w x) = 1)

    (ι : ∀ w : HeightOneSpectrum (𝓞 F), (w.adicCompletion F)ˣ →* (AdeleRing (𝓞 F) F)ˣ)
    (hι : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ),
      finPart w (ι w x) = x ∧ (∀ w' : HeightOneSpectrum (𝓞 F), w' ≠ w → finPart w' (ι w x) = 1) ∧ infPart (ι w x) = 1)

    (W : HeightOneSpectrum (𝓞 F'))
    (r : ↥(NumberField.PlaceDecomp.decomp E F' W) →* ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))))
    (hr : ∀ (σ : ↥(NumberField.PlaceDecomp.decomp E F' W)) (x : F),
      algebraMap F F' (((r σ : ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) : F ≃ₐ[E] F) x) = (σ : F' ≃ₐ[E] F') (algebraMap F F' x))
    (hle : NumberField.PlaceDecomp.decomp E F' W ≤
      (NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)))

    (iW : Rep.res r (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) ((W.under (𝓞 F)).adicCompletion F)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F' W)) (W.adicCompletion F')ˣ)
    (hiW : ∀ x : ((W.under (𝓞 F)).adicCompletion F)ˣ,
      ((Additive.toMul (iW.hom (Additive.ofMul x)) : (W.adicCompletion F')ˣ) : W.adicCompletion F') =
        HeightOneSpectrum.Extension.adicCompletionSemialgHom F F' (⟨W, rfl⟩ : (W.under (𝓞 F)).Extension (𝓞 F')) (x : (W.under (𝓞 F)).adicCompletion F))

    (κ : Rep.res ((AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)).subgroupComap (NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))))
          (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) ((W.under (𝓞 F)).adicCompletion F)ˣ) ⟶
        Rep.res ((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))).subtype
          (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')))
    (hκ : ∀ x : ((W.under (𝓞 F)).adicCompletion F)ˣ, κ.hom (Additive.ofMul x) =
      Additive.ofMul (QuotientGroup.mk (Units.map (M4aHerbrand.Bridge.genuineβ F F' : AdeleRing (𝓞 F) F →+* AdeleRing (𝓞 F') F') (ι (W.under (𝓞 F)) x)) : IdeleClassGroup (𝓞 F') F'))

    (φW : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F' W)) (W.adicCompletion F')ˣ ⟶
        Rep.res (Subgroup.inclusion hle)
          (Rep.res ((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))).subtype
            (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F'))))
    (hφW : ∀ x : (W.adicCompletion F')ˣ, φW.hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk (ι' W x) : IdeleClassGroup (𝓞 F') F'))
    (k : ℤ)
    (z : groupCohomology (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) ((W.under (𝓞 F)).adicCompletion F)ˣ) 2)
    (y : groupCohomology (Rep.res ((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))).subtype
          (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F'))) 2)
    (hy : k • (groupCohomology.map (Subgroup.inclusion hle)
            (𝟙 (Rep.res (Subgroup.inclusion hle)
              (Rep.res ((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F))).subtype
                (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F'))))) 2).hom y =
          k • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F' W)) φW 2).hom ((groupCohomology.map r iW 2).hom z)) :
    k • (groupCohomology.map ((AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)).subgroupComap (NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) κ 2).hom z =
      k • ((((NumberField.PlaceDecomp.decomp E F' W).subgroupOf
              ((NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).comap (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)))).index : ℤ) • y) := by sorry
