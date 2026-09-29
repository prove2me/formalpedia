-- Prove2me | Theorems.Thm_M4aHerbrand_exists_invariant_forall_inv_map_eq_finsum_of_forall_localFundamentalClass_of_isPGroup
-- name    : M4aHerbrand.exists_invariant_forall_inv_map_eq_finsum_of_forall_localFundamentalClass_of_isPGroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/74eced24-a3b2-54b3-8815-862c86da2c51
-- title:
--   Tate's reciprocity law for idèle classes, p-group case
-- statement:
--   Throughout, $E$ and $F$ are number fields with $F/E$ Galois, $G$ denotes the Galois group `F ≃ₐ[E] F`, $\mathbb{I}_F$ denotes the unit group $(\mathrm{AdeleRing}(\mathcal O_F,F))^\times$ of the adèle ring, and $C_F$ denotes `IdeleClassGroup (𝓞 F) F`, the quotient of $\mathbb{I}_F$ by the subgroup `principalIdeles (𝓞 F) F`. A datum $D$ of type `IdeleGaloisDescent (𝓞 F) E F` is given: a monoid homomorphism from $G$ to the ring automorphisms of the adèle ring, compatible with the structure map $F \to \mathrm{AdeleRing}(\mathcal O_F,F)$ in the sense that it transports $x \in F$ to $g(x)$, and continuous for each $g$. Multiplicative distributive actions of $G$ on $\mathbb{I}_F$ and on $C_F$ are assumed, and the hypotheses `hactI` and `hact` identify them with the actions coming from $D$: on $\mathbb{I}_F$ with `D.unitsAct g`, the functorial action of the ring automorphism on units, and on $C_F$ with `D.classAct g`, the induced map on the quotient. The hypothesis `hinf` requires that every infinite place $v$ of $F$ have trivial decomposition group, i.e. every $g \in G$ stabilising $v$ equals $1$. Finally $p$ is a prime and `hG` asserts that $G$ is a $p$-group. All cohomology below is group cohomology in degree $2$ of the $\mathbb{Z}$-linear representations `Rep.ofMulDistribMulAction` attached to these multiplicative actions, and $\mathbb{Q}/\mathbb{Z}$ is realised as `AddCircle (1 : ℚ)`.
--
--   The assertion is the existence of an additive invariant map $\mathrm{inv}_G \colon H^2(G, C_F) \to \mathbb{Q}/\mathbb{Z}$ and of a family $\mathrm{inv}_H \colon H^2(H, C_F) \to \mathbb{Q}/\mathbb{Z}$ of additive maps, one for every subgroup $H \le G$ (the module being $C_F$ restricted along `H.subtype`), subject to the following five conjuncts together with the two local–global identities stated afterwards.
--
--   (i) $\mathrm{inv}_G$ is injective. (ii) Each $\mathrm{inv}_H$ is injective. (iii) An element $t \in \mathbb{Q}/\mathbb{Z}$ lies in the range of $\mathrm{inv}_G$ if and only if $|G| \cdot t = 0$. (iv) For every subgroup $H$, an element $t$ lies in the range of $\mathrm{inv}_H$ if and only if $|H| \cdot t = 0$. (v) For every subgroup $H$ and every $x \in H^2(G, C_F)$, the restriction of $x$ to $H$, formed as `groupCohomology.map H.subtype (𝟙 …) 2`, satisfies $\mathrm{inv}_H(\mathrm{res}^G_H x) = [G:H]\cdot \mathrm{inv}_G(x)$, the index being `H.index`.
--
--   (vi) The identity at the full group. For every family $\mathrm{pr}_G$ assigning to each finite place $w$ of $F$ (a height-one prime of $\mathcal O_F$) a morphism of representations of the decomposition group $D_w =$ [`NumberField.PlaceDecomp.decomp E F w`](def/NumberField_PlaceDecompositionAction.html#L82) from the restriction of $\mathbb{I}_F$ to $D_w$ to the units $(F_w)^\times$ of the $w$-adic completion, whose underlying map is the $w$-component homomorphism `finPart w`; for every morphism $\pi$ of $G$-representations from $\mathbb{I}_F$ to $C_F$ whose underlying map is the quotient map; for every class $x \in H^2(G, \mathbb{I}_F)$; and for every system of local data indexed by the finite places $v$ of $E$, consisting of primes $q_v$, finite extensions $L'_v$ and $K_{0,v}$ of $\mathbb{Q}_{q_v}$ inside a fixed algebraic closure `PadicAlgCl (q v)`, an action of $D_{w(v)}$ on $L'_v$ by semiring automorphisms and a compatible multiplicative distributive action on $(L'_v)^\times$ (where $w(v) =$ [`NumberField.PlaceAbove.above E F v`](def/NumberField_PlaceAbove.html#L27) is the chosen place of $F$ above $v$), a ring isomorphism $\Phi_v \colon F_{w(v)} \xrightarrow{\ \sim\ } L'_v$, and morphisms $\theta_v$ of $D_{w(v)}$-representations from $(L'_v)^\times$ to $(F_{w(v)})^\times$, subject to the compatibility hypotheses that the $D_{w(v)}$-action on $L'_v$ fixes $\mathbb{Q}_{q_v}$ pointwise, that the action on $(L'_v)^\times$ is the one on $L'_v$ on underlying elements, that $\Phi_v$ is $D_{w(v)}$-equivariant, that $\theta_v$ is $\Phi_v^{-1}$ on underlying units, that [`ExtCitation.LocalLevel.IsBase (q v) (L' v) D_{w(v)} (K₀ v)`](def/ExtCitation_LocalLevel_FundamentalClass.html#L13) holds — that is, $K_{0,v} \le L'_v$ and an element of $L'_v$ lies in $K_{0,v}$ exactly when it is fixed by all of $D_{w(v)}$ — and that classes $u'_v \in H^2(D_{w(v)}, (L'_v)^\times)$ satisfy [`ExtCitation.LocalLevel.IsLocalFundamentalClass (q v) (L' v) D_{w(v)} (K₀ v) (u' v)`](def/ExtCitation_LocalLevel_FundamentalClass.html#L60), i.e. $u'_v$ is a local fundamental class in the sense that for every presentation of $L'_v/K_{0,v}$ inside a finite extension $M/\mathbb{Q}_{q_v}$ carrying a faithful action of a finite group $H$, with normal subgroups $N_L$ and $N_n$ cutting out $L'_v$ and an unramified layer, an isomorphism $e \colon D_{w(v)} \cong H/N_L$, an element $\varphi$ whose class generates the cyclic quotient $H/N_n$ and acts as the residue-field power map up to higher order, a uniformiser $\pi$ of $K_{0,v}$ in $M$ fixed by $H$ and of minimal norm among $N_n$-invariants (the clauses of `IsUnramOverlayerDatum`, summarised here), and every comparison morphism $\iota$ lifting the inclusion $L'_v \subseteq M$, the image of $u'_v$ under the map induced by $e^{-1}\circ\mathrm{mk}$ and $\iota$ is the inflation from $H/N_n$ of the class of the explicit cyclic carry $2$-cocycle `carryFun` with value $\pi$; and for every $n \colon \{v\} \to \mathbb{Z}$ such that for each finite place $v$ of $E$ the image of $x$ under restriction to $D_{w(v)}$ followed by $\mathrm{pr}_G(w(v))$ equals $n_v$ times the image of $u'_v$ under $\theta_v$ in $H^2(D_{w(v)}, (F_{w(v)})^\times)$ — under all these data one has
--   $$\mathrm{inv}_G\bigl(H^2(\pi)(x)\bigr) \;=\; \sum_{v}{}^{\mathrm{f}} \ \Bigl[\frac{n_v}{|D_{w(v)}|}\Bigr] \in \mathbb{Q}/\mathbb{Z},$$
--   the sum being the `∑ᶠ` sum over all finite places $v$ of $E$ of the classes of the rationals $n_v/|D_{w(v)}|$ modulo $1$.
--
--   (vii) The identity at each subgroup. For every subgroup $H \le G$ the same statement holds with the following replacements. The local coordinate maps $\mathrm{pr}_H$ now attach to each finite place $w$ of $F$ a morphism from the restriction of $\mathbb{I}_F$ along the inclusion $H \cap D_w \le H$ to the restriction of $(F_w)^\times$ along $H \cap D_w \le D_w$, again given by `finPart w` on underlying elements; $\pi_H$ is a morphism of $H$-representations from $\mathbb{I}_F$ to $C_F$ given by the quotient map; $x$ lies in $H^2(H, \mathbb{I}_F)$; the local data $q_v$, $L'_v$, $K_{0,v}$, $\Phi_v$, $\theta_v$, $u'_v$, with the same compatibility, base and local fundamental class conditions, are now indexed by the finite places $v$ of the fixed field `IntermediateField.fixedField H`, the relevant groups being the decomposition groups over $E$ of the chosen places $w(v)$ of $F$ above them; and $n \colon \{v\} \to \mathbb{Z}$ is required to satisfy, for each such $v$, that the image of $x$ under restriction along $H \cap D_{w(v)} \le H$ followed by $\mathrm{pr}_H(w(v))$ equals $n_v$ times the restriction along $H \cap D_{w(v)} \le D_{w(v)}$ of the image of $u'_v$ under $\theta_v$. The conclusion is
--   $$\mathrm{inv}_H\bigl(H^2(\pi_H)(x)\bigr) \;=\; \sum_{v}{}^{\mathrm{f}} \ \Bigl[\frac{n_v}{|H \cap D_{w(v)}|}\Bigr] \in \mathbb{Q}/\mathbb{Z},$$
--   the `∑ᶠ` sum running over the finite places $v$ of the fixed field of $H$.
--
--   This is Tate's reciprocity law for the idèle class formation, in the form asserting the existence of invariant maps on $H^2$ of the idèle class group for a Galois layer and all of its subgroups, injective with image the torsion of the expected order, compatible with restriction up to the index, and computing the invariant of a class coming from the idèles as the sum of its local invariants measured against the local fundamental classes; here the layer is assumed to have $p$-group Galois group and infinite places with trivial decomposition groups. It is used downstream by [`M4aHerbrand.exists_invariant_forall_inv_map_localFundamentalClass_eq_one_div_natCard_decomp_of_isPGroup`](thm.html#M4aHerbrand.exists_invariant_forall_inv_map_localFundamentalClass_eq_one_div_natCard_decomp_of_isPGroup), by [`M4aHerbrand.map_pi_eq_zero_iff_finsum_eq_zero_of_pow_smul_eq_zero`](thm.html#M4aHerbrand.map_pi_eq_zero_iff_finsum_eq_zero_of_pow_smul_eq_zero) and by [`NumberField.LevelArith.exists_level_d_two_three_eq_of_sIdele_coboundary_of_smul_eq_of_dvd_natCard_decomp`](thm.html#NumberField.LevelArith.exists_level_d_two_three_eq_of_sIdele_coboundary_of_smul_eq_of_dvd_natCard_decomp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_exists_invariant_forall_inv_map_eq_finsum_of_forall_localFundamentalClass_of_isPGroup.lean

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open CategoryTheory NumberField IsDedekindDomain
open M4aHerbrand
open scoped NumberField.PlaceDecomp

theorem M4aHerbrand.exists_invariant_forall_inv_map_eq_finsum_of_forall_localFundamentalClass_of_isPGroup
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (D : IdeleGaloisDescent (𝓞 F) E F)

    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
    (hactI : ∀ (g : (F ≃ₐ[E] F)) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x)
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (hact : ∀ (g : (F ≃ₐ[E] F)) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c)

    (hinf : ∀ (v : InfinitePlace F) (g : (F ≃ₐ[E] F)), g ∈ NumberField.InfPlaceDecomp.decomp E F v → g = 1)

    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p (F ≃ₐ[E] F)) :
    ∃ (invG : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2) →+ AddCircle (1 : ℚ))
      (inv : ∀ H : Subgroup (F ≃ₐ[E] F), ↥(groupCohomology (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2) →+ AddCircle (1 : ℚ)),

      Function.Injective invG ∧ (∀ H : Subgroup (F ≃ₐ[E] F), Function.Injective (inv H)) ∧
      (∀ t : AddCircle (1 : ℚ), t ∈ invG.range ↔ Nat.card (F ≃ₐ[E] F) • t = 0) ∧
      (∀ (H : Subgroup (F ≃ₐ[E] F)) (t : AddCircle (1 : ℚ)), t ∈ (inv H).range ↔ Nat.card ↥H • t = 0) ∧

      (∀ (H : Subgroup (F ≃ₐ[E] F)) (x : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2)),
        inv H ((groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))) 2).hom x) = H.index • invG x) ∧

      (∀

        (prG : ∀ w : HeightOneSpectrum (𝓞 F),
          Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
            Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
        (_ : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ), (prG w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))

        (π : Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ ⟶ Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))
        (_ : ∀ x : (AdeleRing (𝓞 F) F)ˣ, π.hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk x : IdeleClassGroup (𝓞 F) F))
        (x : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) 2))

        (q : HeightOneSpectrum (𝓞 E) → ℕ) (_ : ∀ v, Fact (q v).Prime)
        (L' : ∀ v : HeightOneSpectrum (𝓞 E), IntermediateField ℚ_[q v] (PadicAlgCl (q v)))
        (_ : ∀ v, FiniteDimensional ℚ_[q v] (L' v))
        (_ : ∀ v : HeightOneSpectrum (𝓞 E), MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (L' v))
        (_ : ∀ v : HeightOneSpectrum (𝓞 E), MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L' v))ˣ)
        (Φ : ∀ v : HeightOneSpectrum (𝓞 E), (NumberField.PlaceAbove.above E F v).adicCompletion F ≃+* L' v)
        (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : ℚ_[q v]), g • algebraMap ℚ_[q v] (L' v) y = algebraMap ℚ_[q v] (L' v) y)
        (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : (↥(L' v))ˣ), ((g • y : (↥(L' v))ˣ) : L' v) = g • (y : L' v))
        (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : (NumberField.PlaceAbove.above E F v).adicCompletion F), (Φ v) (g • y) = g • (Φ v) y)
        (K₀ : ∀ v : HeightOneSpectrum (𝓞 E), IntermediateField ℚ_[q v] (PadicAlgCl (q v)))
        (_ : ∀ v, FiniteDimensional ℚ_[q v] (K₀ v))
        (_ : ∀ v : HeightOneSpectrum (𝓞 E), ExtCitation.LocalLevel.IsBase (q v) (L' v) (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (K₀ v))
        (θ : ∀ v : HeightOneSpectrum (𝓞 E), Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L' v))ˣ ⟶
          Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) ((NumberField.PlaceAbove.above E F v).adicCompletion F)ˣ)
        (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (y : (↥(L' v))ˣ),
          ((Additive.toMul ((θ v).hom (Additive.ofMul y)) : ((NumberField.PlaceAbove.above E F v).adicCompletion F)ˣ) : (NumberField.PlaceAbove.above E F v).adicCompletion F) =
            (Φ v).symm (y : L' v))
        (u' : ∀ v : HeightOneSpectrum (𝓞 E), groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L' v))ˣ))
        (_ : ∀ v : HeightOneSpectrum (𝓞 E), ExtCitation.LocalLevel.IsLocalFundamentalClass (q v) (L' v) (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (K₀ v) (u' v))

        (n : HeightOneSpectrum (𝓞 E) → ℤ)
        (_ : ∀ v : HeightOneSpectrum (𝓞 E),
          (groupCohomology.map (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)).subtype (prG (NumberField.PlaceAbove.above E F v)) 2).hom x =
            n v • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (θ v) 2).hom (u' v)),
        invG ((groupCohomology.map (MonoidHom.id (F ≃ₐ[E] F)) π 2).hom x) =
          ∑ᶠ v : HeightOneSpectrum (𝓞 E), ((((n v : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) : ℚ) : ℚ) : AddCircle (1 : ℚ)))) ∧

      (∀ (H : Subgroup (F ≃ₐ[E] F))

        (prH : ∀ w : HeightOneSpectrum (𝓞 F),
          Rep.res (Subgroup.inclusion (inf_le_left : H ⊓ (NumberField.PlaceDecomp.decomp E F w) ≤ H)) (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ)) ⟶
            Rep.res (Subgroup.inclusion (inf_le_right : H ⊓ (NumberField.PlaceDecomp.decomp E F w) ≤ (NumberField.PlaceDecomp.decomp E F w)))
              (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ))
        (_ : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ), (prH w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))

        (πH : Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶ Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))
        (_ : ∀ x : (AdeleRing (𝓞 F) F)ˣ, πH.hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk x : IdeleClassGroup (𝓞 F) F))
        (x : ↥(groupCohomology (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ)) 2))

        (q : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)) → ℕ) (_ : ∀ v, Fact (q v).Prime)
        (L' : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), IntermediateField ℚ_[q v] (PadicAlgCl (q v)))
        (_ : ∀ v, FiniteDimensional ℚ_[q v] (L' v))
        (_ : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (L' v))
        (_ : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (↥(L' v))ˣ)
        (Φ : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v).adicCompletion F ≃+* L' v)
        (_ : ∀ (v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H))) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (y : ℚ_[q v]), g • algebraMap ℚ_[q v] (L' v) y = algebraMap ℚ_[q v] (L' v) y)
        (_ : ∀ (v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H))) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (y : (↥(L' v))ˣ), ((g • y : (↥(L' v))ˣ) : L' v) = g • (y : L' v))
        (_ : ∀ (v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H))) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (y : (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v).adicCompletion F), (Φ v) (g • y) = g • (Φ v) y)
        (K₀ : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), IntermediateField ℚ_[q v] (PadicAlgCl (q v)))
        (_ : ∀ v, FiniteDimensional ℚ_[q v] (K₀ v))
        (_ : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), ExtCitation.LocalLevel.IsBase (q v) (L' v) (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (K₀ v))
        (θ : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (↥(L' v))ˣ ⟶
          Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) ((NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v).adicCompletion F)ˣ)
        (_ : ∀ (v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H))) (y : (↥(L' v))ˣ),
          ((Additive.toMul ((θ v).hom (Additive.ofMul y)) : ((NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v).adicCompletion F)ˣ) : (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v).adicCompletion F) =
            (Φ v).symm (y : L' v))
        (u' : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (↥(L' v))ˣ))
        (_ : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), ExtCitation.LocalLevel.IsLocalFundamentalClass (q v) (L' v) (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (K₀ v) (u' v))

        (n : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)) → ℤ)
        (_ : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)),
          (groupCohomology.map (Subgroup.inclusion (inf_le_left : H ⊓ (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v)) ≤ H)) (prH (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v)) 2).hom x =
            n v • (groupCohomology.map (Subgroup.inclusion (inf_le_right : H ⊓ (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v)) ≤ (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))))
              (𝟙 (Rep.res (Subgroup.inclusion (inf_le_right : H ⊓ (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v)) ≤ (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))))
                (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) ((NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v).adicCompletion F)ˣ))) 2).hom
              ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (θ v) 2).hom (u' v))),
        inv H ((groupCohomology.map (MonoidHom.id ↥H) πH 2).hom x) =
          ∑ᶠ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), ((((n v : ℚ) / (Nat.card ↥(H ⊓ (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) : ℚ) : ℚ) : AddCircle (1 : ℚ)))) := by sorry
