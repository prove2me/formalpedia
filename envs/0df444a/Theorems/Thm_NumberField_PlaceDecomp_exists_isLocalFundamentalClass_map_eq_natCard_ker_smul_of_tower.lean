-- Prove2me | Theorems.Thm_NumberField_PlaceDecomp_exists_isLocalFundamentalClass_map_eq_natCard_ker_smul_of_tower
-- name    : NumberField.PlaceDecomp.exists_isLocalFundamentalClass_map_eq_natCard_ker_smul_of_tower
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/0e40f93d-96cd-56b9-91cb-743d30d16664
-- title:
--   Local fundamental classes along a tower of decomposition groups
-- statement:
--   Let $E \subseteq F \subseteq M$ be number fields forming a scalar tower with $F/E$ and $M/E$ Galois, let $W$ be a height-one prime of $\mathcal O_M$ and write $w = W \cap \mathcal O_F$ for `W.under (𝓞 F)`; let $D_W =$ `decomp E M W` and $D_w =$ `decomp E F (W.under (𝓞 F))` be the decomposition subgroups of $M \simeq_E M$ and $F \simeq_E F$ attached to the valuation subrings of the $W$- and $w$-adic valuations, both assumed solvable. Assume given a monoid homomorphism $r : D_W \to D_w$ with $\iota_{F,M}(r(\sigma)(x)) = \sigma(\iota_{F,M}(x))$ for all $x \in F$, and a morphism $iD$ from the restriction along $r$ of the representation on $(F_w)^{\times}$ to the representation on $(M_W)^{\times}$ (both arising from the multiplicative actions on units of the adic completions) whose underlying map on units is induced by `HeightOneSpectrum.Extension.adicCompletionSemialgHom` for the extension $W$ of $w$. Fix a prime $q$ and finite extensions $L \le L''$ of $\mathbb Q_q$ inside `PadicAlgCl q`, with faithful multiplicative semiring actions of $D_w$ on $L$ and of $D_W$ on $L''$ together with the corresponding actions on unit groups, and ring isomorphisms $\Phi : F_w \cong L$, $\Phi'' : M_W \cong L''$; assume $\Phi$ and $\Phi''$ equivariant, the actions trivial on $\mathbb Q_q$-scalars, the unit actions compatible with the coercions to $L$ and $L''$, and $\Phi''$ composed with the completion embedding $F_w \to M_W$ equal to $\Phi$ inside `PadicAlgCl q`. Then there exist a finite extension $K_0$ of $\mathbb Q_q$ inside `PadicAlgCl q`, morphisms of representations $\theta$ from $L^{\times}$ to $(F_w)^{\times}$ over $D_w$ and $\theta''$ from $(L'')^{\times}$ to $(M_W)^{\times}$ over $D_W$, and classes $u \in H^2(D_w, L^{\times})$, $u'' \in H^2(D_W, (L'')^{\times})$ such that: $K_0 \le L$ and an element of $L$ lies in $K_0$ exactly when it is fixed by all of $D_w$, and likewise $K_0 \le L''$ with $K_0$ the $D_W$-fixed part of $L''$; $\theta$ and $\theta''$ act on underlying elements by $\Phi^{-1}$ and $(\Phi'')^{-1}$; $u$ and $u''$ satisfy `IsLocalFundamentalClass` over $K_0$, i.e. for every unramified overlayer datum above the layer (an overfield $M'$, a finite group $H$ acting faithfully with the prescribed base, layer, Frobenius and uniformiser conditions, an isomorphism of the group with $H$ modulo the layer subgroup, and a compatible unit map) the inflated class is the class of the cyclic carry cocycle built from the uniformiser; moreover $$H^2(r, iD)(\theta_* u) = |\ker r| \cdot \theta''_*(u'')$$ in $H^2(D_W, (M_W)^{\times})$, and $|D_W| = |\ker r| \cdot |D_w|$.
--
--   This is the tower form of the inflation relation $\mathrm{inf}\, u_{L/K} = [L':L]\, u_{L'/K}$ for local fundamental classes, transported to the decomposition groups of a place $W$ of $M$ and its restriction to $F$, and phrased through explicit identifications of the completions $F_w$ and $M_W$ with finite extensions of $\mathbb Q_q$ inside a fixed algebraic closure. It feeds the comparison of Herbrand-type quotients for decomposition groups in a tower and the construction of the fundamental class of the idele class group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceDecomp_exists_isLocalFundamentalClass_map_eq_natCard_ker_smul_of_tower.lean

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3
open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField.PlaceDecomp

theorem NumberField.PlaceDecomp.exists_isLocalFundamentalClass_map_eq_natCard_ker_smul_of_tower
    (E F M : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field M] [NumberField M]
    [Algebra E F] [Algebra E M] [Algebra F M] [IsScalarTower E F M] [IsGalois E F] [IsGalois E M]
    (W : HeightOneSpectrum (𝓞 M))
    (hsolv : Group.IsSolvable ↥(NumberField.PlaceDecomp.decomp E M W))
    (hsolv₁ : Group.IsSolvable ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))))

    (r : ↥(NumberField.PlaceDecomp.decomp E M W) →* ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))))
    (hr : ∀ (σ : ↥(NumberField.PlaceDecomp.decomp E M W)) (x : F),
      algebraMap F M (((r σ : ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) : F ≃ₐ[E] F) x) = (σ : M ≃ₐ[E] M) (algebraMap F M x))
    (iD : Rep.res r (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) ((W.under (𝓞 F)).adicCompletion F)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M W)) (W.adicCompletion M)ˣ)
    (hiD : ∀ x : ((W.under (𝓞 F)).adicCompletion F)ˣ,
      ((Additive.toMul (iD.hom (Additive.ofMul x)) : (W.adicCompletion M)ˣ) : W.adicCompletion M) =
        HeightOneSpectrum.Extension.adicCompletionSemialgHom F M (⟨W, rfl⟩ : (W.under (𝓞 F)).Extension (𝓞 M)) (x : (W.under (𝓞 F)).adicCompletion F))

    (q : ℕ) [Fact q.Prime] (L L'' : IntermediateField ℚ_[q] (PadicAlgCl q)) (hLL'' : L ≤ L'')
    [FiniteDimensional ℚ_[q] L] [FiniteDimensional ℚ_[q] L'']
    [MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) L]
    [FaithfulSMul (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) L]
    [MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) (↥L)ˣ]
    [MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E M W)) L''] [FaithfulSMul (↥(NumberField.PlaceDecomp.decomp E M W)) L'']
    [MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M W)) (↥L'')ˣ]
    (Φ : (W.under (𝓞 F)).adicCompletion F ≃+* L) (Φ'' : W.adicCompletion M ≃+* L'')
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) (x : (W.under (𝓞 F)).adicCompletion F), Φ (g • x) = g • Φ x)
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E M W)) (x : W.adicCompletion M), Φ'' (g • x) = g • Φ'' x)
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E M W)) (x : ℚ_[q]), g • algebraMap ℚ_[q] L'' x = algebraMap ℚ_[q] L'' x)
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) (u : (↥L)ˣ), ((g • u : (↥L)ˣ) : L) = g • (u : L))
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E M W)) (u : (↥L'')ˣ), ((g • u : (↥L'')ˣ) : L'') = g • (u : L''))
    (_ : ∀ x : (W.under (𝓞 F)).adicCompletion F,
      ((Φ'' (HeightOneSpectrum.Extension.adicCompletionSemialgHom F M
          (⟨W, rfl⟩ : (W.under (𝓞 F)).Extension (𝓞 M)) x) : L'') : PadicAlgCl q) = ((Φ x : L) : PadicAlgCl q)) :
    ∃ (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) (_ : FiniteDimensional ℚ_[q] K₀)
      (θ : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) (↥L)ˣ ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) ((W.under (𝓞 F)).adicCompletion F)ˣ)
      (θ'' : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M W)) (↥L'')ˣ ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M W)) (W.adicCompletion M)ˣ)
      (u : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) (↥L)ˣ))
      (u'' : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M W)) (↥L'')ˣ)),
      ExtCitation.LocalLevel.IsBase q L (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) K₀ ∧
      ExtCitation.LocalLevel.IsBase q L'' (↥(NumberField.PlaceDecomp.decomp E M W)) K₀ ∧
      (∀ y : (↥L)ˣ, ((Additive.toMul (θ.hom (Additive.ofMul y)) : ((W.under (𝓞 F)).adicCompletion F)ˣ) : (W.under (𝓞 F)).adicCompletion F) = Φ.symm (y : L)) ∧
      (∀ y : (↥L'')ˣ, ((Additive.toMul (θ''.hom (Additive.ofMul y)) : (W.adicCompletion M)ˣ) : W.adicCompletion M) = Φ''.symm (y : L'')) ∧
      ExtCitation.LocalLevel.IsLocalFundamentalClass q L (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) K₀ u ∧
      ExtCitation.LocalLevel.IsLocalFundamentalClass q L'' (↥(NumberField.PlaceDecomp.decomp E M W)) K₀ u'' ∧
      (groupCohomology.map r iD 2).hom ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) θ 2).hom u) =
        Nat.card ↥r.ker • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E M W)) θ'' 2).hom u'' ∧
      Nat.card ↥(NumberField.PlaceDecomp.decomp E M W) = Nat.card ↥r.ker * Nat.card ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))) := by sorry
