-- Prove2me | Theorems.Thm_M4aHerbrand_div_natCard_decomp_eq_div_natCard_decomp_under_of_map_map_eq_zsmul_of_isScalarTower
-- name    : M4aHerbrand.div_natCard_decomp_eq_div_natCard_decomp_under_of_map_map_eq_zsmul_of_isScalarTower
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/3450deaf-b6da-5f71-a5c9-8e862e738569
-- title:
--   Local invariants unchanged by inflation, numerical form
-- statement:
--   Let $E \subseteq F \subseteq M$ be number fields (a scalar tower, with $F/E$ and $M/E$ Galois) and fix multiplicative actions of $\mathrm{Gal}(F/E)$ and $\mathrm{Gal}(M/E)$ on the idèle groups $(\mathbb{A}_F)^\times$, $(\mathbb{A}_M)^\times$. Let $S \trianglelefteq \mathrm{Gal}(M/E)$ and $\iota \colon \mathrm{Gal}(M/E)/S \cong \mathrm{Gal}(F/E)$ be an isomorphism compatible with restriction, in the sense that $\iota(\bar g)$ followed by $F \to M$ agrees with $g$ on the image of $F$. Let $J$ be a morphism of representations from the restriction of the $F$-idèle module along $\iota \circ \mathrm{mk}'$ to the $M$-idèle module which, on elements, is the map on units induced by the ring homomorphism $\beta$ of the adèle base change `genuineBaseChange F M`. Fix a finite place $W$ of $M$, write $w_1 = W \cap \mathcal{O}_F$, and let $D_W$, $D_{w_1}$ be the decomposition subgroups (stabilisers of the valuation subrings) of $W$ in $\mathrm{Gal}(M/E)$ and of $w_1$ in $\mathrm{Gal}(F/E)$. Let $\mathrm{prG}$, $\mathrm{prM}$ be morphisms of representations from the restrictions of the idèle modules to $D_{w_1}$, $D_W$ onto the units of the completions $F_{w_1}$, $M_W$, given on elements by the $w_1$- resp. $W$-component `finPart`. Let $y$ be a degree-$2$ cohomology class of $\mathrm{Gal}(F/E)$ acting on $(\mathbb{A}_F)^\times$. At $w_1$ there is given local bridge data: a prime $q$, a finite extension $L' \subseteq \overline{\mathbb{Q}}_q$ of $\mathbb{Q}_q$ with a $D_{w_1}$-semiring action and a compatible action on $(L')^\times$, a ring isomorphism $\Phi \colon F_{w_1} \cong L'$ which is $D_{w_1}$-equivariant, the action being trivial on $\mathbb{Q}_q$-scalars and compatible with the unit action, a finite base field $K_0$ satisfying `IsBase`, i.e. $K_0 \le L'$ and an element of $L'$ lies in $K_0$ exactly when it is fixed by all of $D_{w_1}$, a morphism $\theta$ from $(L')^\times$ to $F_{w_1}^\times$ given by $\Phi^{-1}$, and a class $u \in H^2(D_{w_1}, (L')^\times)$ satisfying `IsLocalFundamentalClass` (for every unramified overlayer datum above $L'$, the inflation of $u$ is the class of the carry $2$-cocycle built from the Frobenius lift and the uniformiser of the datum); and an integer $n$ with the hypothesis that the image of $y$ under the degree-$2$ map along the inclusion $D_{w_1} \hookrightarrow \mathrm{Gal}(F/E)$ and $\mathrm{prG}$ equals $n$ times the image of $u$ along $\theta$. Analogous bridge data $q_M$, $L_M$, $\Phi_M$, $K_M$, $\theta_M$, $u_M$ at $W$, together with an integer $n_M$, is assumed, with the hypothesis that the $W$-component of the class obtained from $y$ by the degree-$2$ map along $\iota \circ \mathrm{mk}'$ and $J$ equals $n_M$ times the image of $u_M$ along $\theta_M$. The conclusion is the equality $$\frac{n_M}{|D_W|} = \frac{n}{|D_{w_1}|}$$ in $\mathbb{Q}/\mathbb{Z}$, realised as `AddCircle (1 : ℚ)`.
--
--   This is the numerical form of the statement that local invariants are unchanged by inflation, $\mathrm{inv}_W(\mathrm{inf}\, c) = \mathrm{inv}_{w_1}(c)$, expressed through explicit bridges identifying the completions with finite extensions of $\mathbb{Q}_q$ and through the integers measuring the local components against local fundamental classes. It feeds the comparison of sums of local invariants under base change of idèles and the transfer of local invertibility from a field to a larger one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_div_natCard_decomp_eq_div_natCard_decomp_under_of_map_map_eq_zsmul_of_isScalarTower.lean

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3
open CategoryTheory NumberField IsDedekindDomain
open M4aHerbrand
open scoped NumberField.PlaceDecomp

theorem M4aHerbrand.div_natCard_decomp_eq_div_natCard_decomp_under_of_map_map_eq_zsmul_of_isScalarTower
    (E F M : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field M] [NumberField M]
    [Algebra E F] [Algebra E M] [Algebra F M] [IsScalarTower E F M] [IsGalois E F] [IsGalois E M]
    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ] [MulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ]

    (S : Subgroup (M ≃ₐ[E] M)) [S.Normal] (ι : (M ≃ₐ[E] M) ⧸ S ≃* (F ≃ₐ[E] F))
    (hι : ∀ (g : M ≃ₐ[E] M) (x : F), algebraMap F M (ι (QuotientGroup.mk g) x) = g (algebraMap F M x))

    (J : Rep.res (ι.toMonoidHom.comp (QuotientGroup.mk' S)) (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
          Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ)
    (hJ : ∀ x : (AdeleRing (𝓞 F) F)ˣ, J.hom (Additive.ofMul x) =
        Additive.ofMul (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange F M).β.toMonoidHom x))

    (W : HeightOneSpectrum (𝓞 M))
    (prG : Rep.res (NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) ((W.under (𝓞 F)).adicCompletion F)ˣ)
    (hprG : ∀ x : (AdeleRing (𝓞 F) F)ˣ, prG.hom (Additive.ofMul x) = Additive.ofMul (finPart (W.under (𝓞 F)) x))
    (prM : Rep.res (NumberField.PlaceDecomp.decomp E M W).subtype (Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M W)) (W.adicCompletion M)ˣ)
    (hprM : ∀ x : (AdeleRing (𝓞 M) M)ˣ, prM.hom (Additive.ofMul x) = Additive.ofMul (finPart W x))
    (y : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) 2))

    (q : ℕ) [Fact q.Prime] (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L']
    [MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) L']
    [MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) (↥L')ˣ]
    (Φ : (W.under (𝓞 F)).adicCompletion F ≃+* L')
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) (y : ℚ_[q]), g • algebraMap ℚ_[q] L' y = algebraMap ℚ_[q] L' y)
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) (y : (↥L')ˣ), ((g • y : (↥L')ˣ) : L') = g • (y : L'))
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) (y : (W.under (𝓞 F)).adicCompletion F), Φ (g • y) = g • Φ y)
    (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀]
    (_ : ExtCitation.LocalLevel.IsBase q L' (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) K₀)
    (θ : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) (↥L')ˣ ⟶
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) ((W.under (𝓞 F)).adicCompletion F)ˣ)
    (_ : ∀ y : (↥L')ˣ, ((Additive.toMul (θ.hom (Additive.ofMul y)) : ((W.under (𝓞 F)).adicCompletion F)ˣ) : (W.under (𝓞 F)).adicCompletion F) = Φ.symm (y : L'))
    (u : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) (↥L')ˣ))
    (_ : ExtCitation.LocalLevel.IsLocalFundamentalClass q L' (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) K₀ u)
    (n : ℤ)
    (_ : (groupCohomology.map (NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).subtype prG 2).hom y =
        n • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) θ 2).hom u)

    (qM : ℕ) [Fact qM.Prime] (LM : IntermediateField ℚ_[qM] (PadicAlgCl qM)) [FiniteDimensional ℚ_[qM] LM]
    [MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E M W)) LM]
    [MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M W)) (↥LM)ˣ]
    (ΦM : W.adicCompletion M ≃+* LM)
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E M W)) (y : ℚ_[qM]), g • algebraMap ℚ_[qM] LM y = algebraMap ℚ_[qM] LM y)
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E M W)) (y : (↥LM)ˣ), ((g • y : (↥LM)ˣ) : LM) = g • (y : LM))
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E M W)) (y : W.adicCompletion M), ΦM (g • y) = g • ΦM y)
    (KM : IntermediateField ℚ_[qM] (PadicAlgCl qM)) [FiniteDimensional ℚ_[qM] KM]
    (_ : ExtCitation.LocalLevel.IsBase qM LM (↥(NumberField.PlaceDecomp.decomp E M W)) KM)
    (θM : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M W)) (↥LM)ˣ ⟶
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M W)) (W.adicCompletion M)ˣ)
    (_ : ∀ y : (↥LM)ˣ, ((Additive.toMul (θM.hom (Additive.ofMul y)) : (W.adicCompletion M)ˣ) : W.adicCompletion M) = ΦM.symm (y : LM))
    (uM : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M W)) (↥LM)ˣ))
    (_ : ExtCitation.LocalLevel.IsLocalFundamentalClass qM LM (↥(NumberField.PlaceDecomp.decomp E M W)) KM uM)
    (nM : ℤ)
    (_ : (groupCohomology.map (NumberField.PlaceDecomp.decomp E M W).subtype prM 2).hom
          ((groupCohomology.map (ι.toMonoidHom.comp (QuotientGroup.mk' S)) J 2).hom y) =
        nM • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E M W)) θM 2).hom uM) :
    (((nM : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E M W) : ℚ) : ℚ) : AddCircle (1 : ℚ)) =
      (((n : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))) : ℚ) : ℚ) : AddCircle (1 : ℚ)) := by sorry
