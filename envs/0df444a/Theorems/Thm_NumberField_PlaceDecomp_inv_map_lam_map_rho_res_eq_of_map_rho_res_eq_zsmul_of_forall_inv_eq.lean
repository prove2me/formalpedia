-- Prove2me | Theorems.Thm_NumberField_PlaceDecomp_inv_map_lam_map_rho_res_eq_of_map_rho_res_eq_zsmul_of_forall_inv_eq
-- name    : NumberField.PlaceDecomp.inv_map_lam_map_rho_res_eq_of_map_rho_res_eq_zsmul_of_forall_inv_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/8f056e65-4460-52f8-9981-cd8203d0501a
-- title:
--   Invariant at w of the descended class equals efm/p
-- statement:
--   Let $E \subseteq F$ be number fields with $F/\mathbb{Q}$ and $F/E$ Galois, and let $r \colon \mathrm{Gal}(F/E) \to \mathrm{Gal}(F/\mathbb{Q})$ be a monoid homomorphism acting on $F$ as the identity inclusion. Let $p$ be prime, $w$ a nonzero prime of $\mathcal{O}_F$, and $q$ a prime with $q \in w$; write $D^{\mathbb{Q}}_w =$ `decomp ℚ F w` and $D^{E}_w =$ `decomp E F w` for the decomposition subgroups of the $w$-adic valuation subring in $\mathrm{Gal}(F/\mathbb{Q})$, resp. $\mathrm{Gal}(F/E)$, and assume $p \mid \lvert D^{\mathbb{Q}}_w \rvert$. Given $x_{\mathbb{Q}} \in H^2(\mathrm{Gal}(F/\mathbb{Q}), F^\times)$, a representation morphism $\varphi$ from the restriction along $r$ of $F^\times$ to $F^\times$ over $\mathrm{Gal}(F/E)$ that is the identity on units, and $x$ the image of $x_{\mathbb{Q}}$ under $H^2$ of $(r,\varphi)$; morphisms $\rho^{\mathbb{Q}}, \rho$ from $F^\times$ restricted to $D^{\mathbb{Q}}_w$, resp. $D^{E}_w$, into the units of the $w$-adic completion $F_w$, each given by the structure map $F \to F_w$. Further data over $\mathbb{Q}_q$: a finite extension $L'$ of $\mathbb{Q}_q$ inside a fixed algebraic closure carrying a faithful $D^{\mathbb{Q}}_w$-action by semiring automorphisms fixing $\mathbb{Q}_q$ and compatible with the action on $(L')^\times$, a ring isomorphism $\Phi' \colon F_w \cong L'$ equivariant for $D^{\mathbb{Q}}_w$, a finite $K_0/\mathbb{Q}_q$ which is a base for $L'$ in the sense that $K_0 \le L'$ and an element of $L'$ lies in $K_0$ exactly when it is fixed by all of $D^{\mathbb{Q}}_w$, a morphism $\theta'$ from $(L')^\times$ to $F_w^\times$ induced by $\Phi'^{-1}$, and a class $u' \in H^2(D^{\mathbb{Q}}_w, (L')^\times)$ satisfying `IsLocalFundamentalClass`, i.e. pulled back along every unramified overlayer datum it becomes the inflation of the class of the cyclic carry cocycle of the uniformiser. Assume that the restriction of $x_{\mathbb{Q}}$ to $D^{\mathbb{Q}}_w$, pushed forward along $\rho^{\mathbb{Q}}$, equals $m \cdot \bigl((\lvert D^{\mathbb{Q}}_w \rvert / p) \cdot \theta'_* u'\bigr)$ for an integer $m$, the quotient being natural-number division. Finally, with $\mathrm{Gal}(F/E)$ acting on the idele class group $C_F = (\mathbb{A}_F)^\times / F^\times$, let $\lambda$ be a morphism from $F_w^\times$ to $C_F$ restricted to $D^{E}_w$, and let $\mathrm{inv}$ assign to each subgroup $H \le \mathrm{Gal}(F/E)$ an additive map $H^2(H, C_F) \to \mathbb{Q}/\mathbb{Z}$, subject to the normalisation that for every analogous layer $L''$, isomorphism $\Phi$, base $K_0''$, transport $\theta$ and every local fundamental class $u''$ for $D^{E}_w$ one has $\mathrm{inv}_{D^{E}_w}(\lambda_* \theta_* u'') = 1/\lvert D^{E}_w \rvert$. The conclusion is that $\mathrm{inv}_{D^{E}_w}$ of the restriction of $x$ to $D^{E}_w$, pushed forward along $\rho$ and then $\lambda$, equals the class in $\mathbb{Q}/\mathbb{Z}$ of $e \cdot f \cdot \mathrm{val}(m \bmod p)/p$, where $e$ and $f$ are `Ideal.ramificationIdx'` and `Ideal.inertiaDeg'` of $q\mathbb{Z}$ at the contraction of $w$ to $\mathcal{O}_E$ and $\mathrm{val}(m \bmod p) \in \{0,\dots,p-1\}$ is the representative of $m$ modulo $p$.
--
--   This is the local-invariant bookkeeping step that converts a normalisation of a degree-two class read off over the rational base at the place $w$ into the value of the invariant map on the decomposition group over the intermediate field $E$, the transition being governed by $\lvert D^{\mathbb{Q}}_w \rvert = e f \lvert D^{E}_w \rvert$ and by the compatibility of local fundamental classes under restriction. It feeds the construction of a $p$-torsion layer with prescribed local invariants in [`groupCohomology.exists_isPGroup_layer_inv_eq_localInv_locRes2S_div_and_sum_inv_eq_zero_of_ne_two`](thm.html#groupCohomology.exists_isPGroup_layer_inv_eq_localInv_locRes2S_div_and_sum_inv_eq_zero_of_ne_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceDecomp_inv_map_lam_map_rho_res_eq_of_map_rho_res_eq_zsmul_of_forall_inv_eq.lean

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology NumberField IsDedekindDomain M4aHerbrand
open scoped NumberField.PlaceDecomp

theorem NumberField.PlaceDecomp.inv_map_lam_map_rho_res_eq_of_map_rho_res_eq_zsmul_of_forall_inv_eq
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois ℚ F] [IsGalois E F]
    (r : (F ≃ₐ[E] F) →* (F ≃ₐ[ℚ] F)) (hr : ∀ (g : F ≃ₐ[E] F) (y : F), r g y = g y)
    (p : ℕ) [Fact p.Prime]
    (w : HeightOneSpectrum (𝓞 F)) (q : ℕ) [Fact q.Prime] (hw : ((q : ℕ) : 𝓞 F) ∈ w.asIdeal)
    (hpD : p ∣ Nat.card ↥(NumberField.PlaceDecomp.decomp ℚ F w))

    (xℚ : groupCohomology.H2 (Rep.ofMulDistribMulAction (F ≃ₐ[ℚ] F) Fˣ))
    (φ : Rep.res r (Rep.ofMulDistribMulAction (F ≃ₐ[ℚ] F) Fˣ) ⟶ Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ)
    (hφ : ∀ u : Fˣ, φ.hom (Additive.ofMul u) = Additive.ofMul u)
    (x : groupCohomology.H2 (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ))
    (hx : x = (groupCohomology.map r φ 2).hom xℚ)
    (ρℚ : Rep.res (NumberField.PlaceDecomp.decomp ℚ F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[ℚ] F) Fˣ) ⟶
        Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ F w) (w.adicCompletion F)ˣ)
    (hρℚ : ∀ u : Fˣ, ρℚ.hom (Additive.ofMul u) = Additive.ofMul (Units.map (algebraMap F (w.adicCompletion F)).toMonoidHom u))
    (ρ : Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
    (hρ : ∀ u : Fˣ, ρ.hom (Additive.ofMul u) = Additive.ofMul (Units.map (algebraMap F (w.adicCompletion F)).toMonoidHom u))

    (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L']
    [MulSemiringAction ↥(NumberField.PlaceDecomp.decomp ℚ F w) L'] [FaithfulSMul ↥(NumberField.PlaceDecomp.decomp ℚ F w) L']
    [MulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ F w) (↥L')ˣ]
    (Φ' : w.adicCompletion F ≃+* L')
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ℚ F w)) (y : ℚ_[q]), g • algebraMap ℚ_[q] L' y = algebraMap ℚ_[q] L' y)
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ℚ F w)) (v : (↥L')ˣ), ((g • v : (↥L')ˣ) : L') = g • (v : L'))
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ℚ F w)) (y : w.adicCompletion F), Φ' (g • y) = g • Φ' y)
    (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀]
    (_ : ExtCitation.LocalLevel.IsBase q L' ↥(NumberField.PlaceDecomp.decomp ℚ F w) K₀)
    (θ' : Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ F w) (↥L')ˣ ⟶
      Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ F w) (w.adicCompletion F)ˣ)
    (_ : ∀ v : (↥L')ˣ, ((Additive.toMul (θ'.hom (Additive.ofMul v)) : (w.adicCompletion F)ˣ) : w.adicCompletion F) = Φ'.symm (v : L'))
    (u' : groupCohomology.H2 (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ F w) (↥L')ˣ))
    (_ : ExtCitation.LocalLevel.IsLocalFundamentalClass q L' ↥(NumberField.PlaceDecomp.decomp ℚ F w) K₀ u')
    (m : ℤ)
    (hm : (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ℚ F w)) ρℚ 2).hom
          ((groupCohomology.map (NumberField.PlaceDecomp.decomp ℚ F w).subtype
            (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp ℚ F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[ℚ] F) Fˣ))) 2).hom xℚ) =
        m • ((Nat.card ↥(NumberField.PlaceDecomp.decomp ℚ F w) / p) •
          (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ℚ F w)) θ' 2).hom u'))

    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (lam : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ ⟶
        Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype
          (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))
    (inv : ∀ H : Subgroup (F ≃ₐ[E] F),
      ↥(groupCohomology (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2) →+
        AddCircle (1 : ℚ))
    (hloc : ∀ (L'' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L'']
        [MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F w)) L'']
        [MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L'')ˣ]
        (Φ : w.adicCompletion F ≃+* L'')
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (x : ℚ_[q]),
          g • algebraMap ℚ_[q] L'' x = algebraMap ℚ_[q] L'' x)
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (v : (↥L'')ˣ), ((g • v : (↥L'')ˣ) : L'') = g • (v : L''))
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (x : w.adicCompletion F), Φ (g • x) = g • Φ x)
        (K₀'' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀'']
        (_ : ExtCitation.LocalLevel.IsBase q L'' (↥(NumberField.PlaceDecomp.decomp E F w)) K₀'')
        (θ : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L'')ˣ ⟶
          Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
        (_ : ∀ v : (↥L'')ˣ,
          ((Additive.toMul (θ.hom (Additive.ofMul v)) : (w.adicCompletion F)ˣ) : w.adicCompletion F) = Φ.symm (v : L''))
        (u'' : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L'')ˣ))
        (_ : ExtCitation.LocalLevel.IsLocalFundamentalClass q L'' (↥(NumberField.PlaceDecomp.decomp E F w)) K₀'' u''),
        inv (NumberField.PlaceDecomp.decomp E F w)
            ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) lam 2).hom
              ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) θ 2).hom u'')) =
          (((1 : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) : ℚ) : ℚ) : AddCircle (1 : ℚ))) :
    inv (NumberField.PlaceDecomp.decomp E F w)
        ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) lam 2).hom
          ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) ρ 2).hom
            ((groupCohomology.map (NumberField.PlaceDecomp.decomp E F w).subtype
              (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype
                (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ))) 2).hom x))) =
      ((((Ideal.ramificationIdx' (Ideal.span {((q : ℕ) : ℤ)}) (Ideal.comap (algebraMap (𝓞 E) (𝓞 F)) w.asIdeal) *
            Ideal.inertiaDeg' (Ideal.span {((q : ℕ) : ℤ)}) (Ideal.comap (algebraMap (𝓞 E) (𝓞 F)) w.asIdeal) *
            ZMod.val (m : ZMod p) : ℕ) : ℚ) / (p : ℚ) : ℚ) : AddCircle (1 : ℚ)) := by sorry
