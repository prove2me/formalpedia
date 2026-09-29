-- Prove2me | Theorems.Thm_M4aHerbrand_exists_fundamentalClass_ideleClassGroup_map_eq_finrank_smul_of_ne_two
-- name    : M4aHerbrand.exists_fundamentalClass_ideleClassGroup_map_eq_finrank_smul_of_ne_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/1aacb957-fa2c-5d00-863f-c1036c9a6f5c
-- title:
--   One-step descent of the idèle-class fundamental class, p odd
-- statement:
--   Fix a prime $p$ with $p \neq 2$, and number fields $E \subseteq F \subseteq F'$, i.e. fields $E$, $F$, $F'$ of finite degree over $\mathbb{Q}$ with algebra structures $E \to F$, $E \to F'$, $F \to F'$ forming a scalar tower, both $F/E$ and $F'/E$ Galois. Write $G = F \simeq_{\mathrm{alg}[E]} F$ and $G' = F' \simeq_{\mathrm{alg}[E]} F'$ for the two Galois groups, and $\pi =$ `AlgEquiv.restrictNormalHom F` $: G' \to G$ for restriction. For a number field $K$, `IdeleClassGroup (𝓞 K) K` is the quotient of $(\mathbb{A}_K)^\times$, the units of `AdeleRing (𝓞 K) K`, by `principalIdeles`, the image of $K^\times$ under `Units.map (algebraMap K (AdeleRing (𝓞 K) K))`; it is viewed additively as an object of `Rep ℤ` via `Rep.ofMulDistribMulAction`. For a finite place $w$ (a height-one prime of $𝓞_K$), [`NumberField.PlaceDecomp.decomp E K w`](def/NumberField_PlaceDecompositionAction.html#L82) is the decomposition subgroup of $\mathrm{Gal}(K/E)$ at the valuation subring of $w$, and `finPart w`, `infPart` are the monoid homomorphisms from $(\mathbb{A}_K)^\times$ to $(K_w)^\times$ and to the units of the infinite adèle ring obtained by functoriality from the $w$-evaluation and the archimedean projection.
--
--   The data at the level of $F$ are: a descent datum `D : IdeleGaloisDescent (𝓞 F) E F`, that is, a homomorphism from $G$ to the ring automorphisms of $\mathbb{A}_F$ whose members are continuous and compatible with $\mathrm{Gal}$ acting on $F \hookrightarrow \mathbb{A}_F$; an action of $G$ on `IdeleClassGroup (𝓞 F) F` by group automorphisms, which `hact` requires to coincide pointwise with the induced action `D.classAct`; for each finite place $w$ of $F$ a homomorphism $\iota_w : (F_w)^\times \to (\mathbb{A}_F)^\times$, with `hι` asserting that $\iota_w$ is the place-$w$ insertion, namely `finPart w (ι w x) = x`, `finPart w' (ι w x) = 1` for every finite place $w' \neq w$, and `infPart (ι w x) = 1`; and for each $w$ a morphism $\lambda_w$ of $\mathbb{Z}$-representations of `decomp E F w` from the additive group of $(F_w)^\times$ to the restriction along the inclusion of the decomposition group of the idèle class group of $F$, with `hlam` asserting that $\lambda_w$ sends $x$ to the idèle class of $\iota_w(x)$.
--
--   The same package is assumed over $F'$: `D'`, an action of $G'$ on `IdeleClassGroup (𝓞 F') F'` with `hact'` identifying it with `D'.classAct`, insertions $\iota'_w$ with the three clauses `hι'`, and morphisms $\lambda'_w$ with `hlam'`.
--
--   The two levels are compared by a morphism $j$ of representations of $G'$ from the restriction along $\pi$ of the idèle class group of $F$ to the idèle class group of $F'$, subject to: `hj`, that $j$ carries the class of $x \in (\mathbb{A}_F)^\times$ to the class of its image under `Units.map` of the base-change ring homomorphism [`M4aHerbrand.Bridge.genuineβ F F' : AdeleRing (𝓞 F) F →+* AdeleRing (𝓞 F') F'`](def/M4aHerbrand_GenuineBeta.html#L14); `hjinj`, that $j$ is injective; and `hjim`, that every element of the idèle class group of $F'$ fixed by all elements of $\ker \pi$ lies in the range of $j$.
--
--   Finally, a class $u_{F'}$ in $H^2(G', C_{F'})$ (`groupCohomology … 2`) is given with two properties. The hypothesis `hord'` states that for every $k \in \mathbb{Z}$ one has $k \cdot u_{F'} = 0$ if and only if $\#G' \mid k$, so $u_{F'}$ has exact order $\#G'$. The hypothesis `hloc'` is a local normalisation at every finite place $w$ of $F'$: for every prime $q$, every finite extension $L'$ of $\mathbb{Q}_q$ inside the fixed algebraic closure `PadicAlgCl q` equipped with actions of $D'_w =$ `decomp E F' w` on $L'$ and on $(L')^\times$, every ring isomorphism $\Phi : F'_w \to L'$, subject to three compatibility clauses (the action of $D'_w$ fixes the image of $\mathbb{Q}_q$, the action on units is compatible with the inclusion $(L')^\times \subseteq L'$, and $\Phi$ is $D'_w$-equivariant), every finite extension $K_0$ of $\mathbb{Q}_q$ in `PadicAlgCl q` with [`ExtCitation.LocalLevel.IsBase q L' D'_w K₀`](def/ExtCitation_LocalLevel_FundamentalClass.html#L13) (i.e. $K_0 \le L'$, and an element of $L'$ lies in $K_0$ exactly when it is fixed by all of $D'_w$), every morphism $\theta$ of representations of $D'_w$ from $(L')^\times$ to $(F'_w)^\times$ whose underlying map is $\Phi^{-1}$ on elements, and every $u' \in H^2(D'_w, (L')^\times)$ satisfying the predicate [`ExtCitation.LocalLevel.IsLocalFundamentalClass q L' D'_w K₀ u'`](def/ExtCitation_LocalLevel_FundamentalClass.html#L60) — which requires that for every unramified overlay $M \supseteq L'$ with a finite faithfully acting group $H$, normal subgroups $N_L, N_n \trianglelefteq H$, an isomorphism $D'_w \cong H/N_L$, an element $\varphi$ and a unit $\pi$ forming an `IsUnramOverlayerDatum` (fixed field conditions for $K_0$ and $L'$, cyclicity of $H/N_n$ generated by the image of $\varphi$, the Frobenius congruence for $\varphi$, and $\pi$ an $H$-fixed element of $K_0$ of maximal norm below one among $N_n$-invariants), and for every equivariant lift $\iota$ of $(L')^\times$ into $M^\times$, the image of $u'$ is the inflation from $H/N_n$ of the class of the cyclic carry $2$-cocycle `carryFun` attached to $\varphi$ and $\pi$ — the conclusion of `hloc'` is that for all natural numbers $m, a$ with $p$ coprime to $m$ and $m p^{a} = \#D'_w$,
--   $$m \cdot H^2(\lambda'_w)\bigl(H^2(\theta)(u')\bigr) = m \cdot \mathrm{res}_{D'_w}(u_{F'}),$$
--   the two maps being `groupCohomology.map` along the identity of $D'_w$ with $\lambda'_w$ resp. $\theta$, and `groupCohomology.map` along the inclusion of $D'_w$ with the identity of the restricted representation.
--
--   Under these hypotheses there exists a class $u_F \in H^2(G, C_F)$, where $C_F$ is the idèle class group of $F$ as a representation of $G$, such that the following four assertions hold.
--
--   First, for every finite subgroup $S \le G$ the cohomology group $H^2(S, \mathrm{Res}_S C_F)$ has cardinality equal to the cardinality of $S$; this conjunct is a statement about $C_F$ alone and does not involve $u_F$.
--
--   Second, for every subgroup $S \le G$ the $\mathbb{Z}$-submodule spanned by the single element $\mathrm{res}_S(u_F)$, the image of $u_F$ under `groupCohomology.map` along the inclusion $S \hookrightarrow G$ together with the identity of the restricted representation, is the whole of $H^2(S, \mathrm{Res}_S C_F)$.
--
--   Third, $u_F$ satisfies the same local normalisation as was assumed for $u_{F'}$: for every finite place $w$ of $F$, every prime $q$, every finite extension $L'$ of $\mathbb{Q}_q$ in `PadicAlgCl q` with actions of $D_w =$ `decomp E F w` on $L'$ and on $(L')^\times$, every ring isomorphism $\Phi : F_w \to L'$ with the three compatibility clauses, every base field $K_0$ with [`ExtCitation.LocalLevel.IsBase q L' D_w K₀`](def/ExtCitation_LocalLevel_FundamentalClass.html#L13), every $\theta$ inducing $\Phi^{-1}$, and every local fundamental class $u' \in H^2(D_w, (L')^\times)$ in the sense of [`ExtCitation.LocalLevel.IsLocalFundamentalClass`](def/ExtCitation_LocalLevel_FundamentalClass.html#L60), one has for all $m, a \in \mathbb{N}$ with $p$ coprime to $m$ and $m p^{a} = \#D_w$,
--   $$m \cdot H^2(\lambda_w)\bigl(H^2(\theta)(u')\bigr) = m \cdot \mathrm{res}_{D_w}(u_F).$$
--
--   Fourth, the map induced in degree $2$ by $\pi$ together with $j$ sends $u_F$ to $[F' : F] \cdot u_{F'}$, the integer being `Module.finrank F F'` acting on $H^2(G', C_{F'})$.
--
--   This is the inductive descent step in the construction of the global fundamental class for the idèle class formation: from a class of exact order $\#\mathrm{Gal}(F'/E)$ over the upper field $F'$, normalised locally at all finite places against local fundamental classes away from $p$, it produces the corresponding class over the intermediate field $F$ together with the inflation relation $H^2(\pi, j)(u_F) = [F':F]\,u_{F'}$. It is used by [`M4aHerbrand.exists_adeleBaseChange_invariant_groupCohomology_ideleClassGroup_map_eq_of_invariant`](thm.html#M4aHerbrand.exists_adeleBaseChange_invariant_groupCohomology_ideleClassGroup_map_eq_of_invariant), and its proof draws on the solvability of decomposition groups, the comparison of local fundamental classes in a tower, and an injectivity criterion for the inflation map in degree $2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_exists_fundamentalClass_ideleClassGroup_map_eq_finrank_smul_of_ne_two.lean

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
open CategoryTheory NumberField IsDedekindDomain
open M4aHerbrand
open scoped NumberField.PlaceDecomp

theorem M4aHerbrand.exists_fundamentalClass_ideleClassGroup_map_eq_finrank_smul_of_ne_two
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (E F F' : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field F'] [NumberField F']
    [Algebra E F] [Algebra E F'] [Algebra F F'] [IsScalarTower E F F'] [IsGalois E F] [IsGalois E F']

    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (hact : ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c)
    (ι : ∀ w : HeightOneSpectrum (𝓞 F), (w.adicCompletion F)ˣ →* (AdeleRing (𝓞 F) F)ˣ)
    (hι : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ),
      finPart w (ι w x) = x ∧ (∀ w' : HeightOneSpectrum (𝓞 F), w' ≠ w → finPart w' (ι w x) = 1) ∧ infPart (ι w x) = 1)
    (lam : ∀ w : HeightOneSpectrum (𝓞 F),
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ ⟶
        Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))
    (hlam : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ),
      (lam w).hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk (ι w x) : IdeleClassGroup (𝓞 F) F))

    (D' : IdeleGaloisDescent (𝓞 F') E F')
    [MulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')]
    (hact' : ∀ (g : F' ≃ₐ[E] F') (c : IdeleClassGroup (𝓞 F') F'), g • c = D'.classAct g c)
    (ι' : ∀ w : HeightOneSpectrum (𝓞 F'), (w.adicCompletion F')ˣ →* (AdeleRing (𝓞 F') F')ˣ)
    (hι' : ∀ (w : HeightOneSpectrum (𝓞 F')) (x : (w.adicCompletion F')ˣ),
      finPart w (ι' w x) = x ∧ (∀ w' : HeightOneSpectrum (𝓞 F'), w' ≠ w → finPart w' (ι' w x) = 1) ∧ infPart (ι' w x) = 1)
    (lam' : ∀ w : HeightOneSpectrum (𝓞 F'),
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F' w)) (w.adicCompletion F')ˣ ⟶
        Rep.res (NumberField.PlaceDecomp.decomp E F' w).subtype (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')))
    (hlam' : ∀ (w : HeightOneSpectrum (𝓞 F')) (x : (w.adicCompletion F')ˣ),
      (lam' w).hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk (ι' w x) : IdeleClassGroup (𝓞 F') F'))
    (j : Rep.res (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)) (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) ⟶ Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F'))
    (hj : ∀ x : (AdeleRing (𝓞 F) F)ˣ, j.hom (Additive.ofMul (QuotientGroup.mk x : IdeleClassGroup (𝓞 F) F)) =
      Additive.ofMul (QuotientGroup.mk (Units.map (M4aHerbrand.Bridge.genuineβ F F' : AdeleRing (𝓞 F) F →+* AdeleRing (𝓞 F') F') x) : IdeleClassGroup (𝓞 F') F'))
    (hjinj : Function.Injective j.hom)
    (hjim : ∀ c' : Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F'), (∀ g' : F' ≃ₐ[E] F', g' ∈ (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)).ker →
      (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')).ρ g' c' = c') → c' ∈ Set.range j.hom)
    (uF' : groupCohomology (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')) 2)
    (hord' : ∀ k : ℤ, k • uF' = 0 ↔ (Nat.card (F' ≃ₐ[E] F') : ℤ) ∣ k)
    (hloc' : ∀ (w : HeightOneSpectrum (𝓞 F'))
        (q : ℕ) [Fact q.Prime] (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L']
        [MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F' w)) L'] [MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F' w)) (↥L')ˣ]
        (Φ : w.adicCompletion F' ≃+* L')
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F' w)) (x : ℚ_[q]), g • algebraMap ℚ_[q] L' x = algebraMap ℚ_[q] L' x)
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F' w)) (v : (↥L')ˣ), ((g • v : (↥L')ˣ) : L') = g • (v : L'))
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F' w)) (x : w.adicCompletion F'), Φ (g • x) = g • Φ x)
        (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀]
        (_ : ExtCitation.LocalLevel.IsBase q L' (↥(NumberField.PlaceDecomp.decomp E F' w)) K₀)
        (θ : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F' w)) (↥L')ˣ ⟶
          Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F' w)) (w.adicCompletion F')ˣ)
        (_ : ∀ v : (↥L')ˣ, ((Additive.toMul (θ.hom (Additive.ofMul v)) : (w.adicCompletion F')ˣ) : w.adicCompletion F') = Φ.symm (v : L'))
        (u' : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F' w)) (↥L')ˣ))
        (_ : ExtCitation.LocalLevel.IsLocalFundamentalClass q L' (↥(NumberField.PlaceDecomp.decomp E F' w)) K₀ u'),
        ∀ (m a : ℕ) (_ : p.Coprime m) (_ : m * p ^ a = Nat.card ↥(NumberField.PlaceDecomp.decomp E F' w)),
        m • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F' w)) (lam' w) 2).hom
              ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F' w)) θ 2).hom u') =
          m • (groupCohomology.map (NumberField.PlaceDecomp.decomp E F' w).subtype
              (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp E F' w).subtype (Rep.ofMulDistribMulAction (F' ≃ₐ[E] F') (IdeleClassGroup (𝓞 F') F')))) 2).hom uF') :
    ∃ uF : groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2,
      (∀ (S : Subgroup (F ≃ₐ[E] F)) [Fintype S], Nat.card
        (groupCohomology (Rep.res S.subtype
          (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2) = Fintype.card S) ∧
      (∀ S : Subgroup (F ≃ₐ[E] F), Submodule.span ℤ
        {(groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype
          (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))) 2).hom uF} = ⊤) ∧
      (∀ (w : HeightOneSpectrum (𝓞 F))
        (q : ℕ) [Fact q.Prime] (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L']
        [MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F w)) L'] [MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ]
        (Φ : w.adicCompletion F ≃+* L')
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (x : ℚ_[q]), g • algebraMap ℚ_[q] L' x = algebraMap ℚ_[q] L' x)
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (v : (↥L')ˣ), ((g • v : (↥L')ˣ) : L') = g • (v : L'))
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (x : w.adicCompletion F), Φ (g • x) = g • Φ x)
        (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀]
        (_ : ExtCitation.LocalLevel.IsBase q L' (↥(NumberField.PlaceDecomp.decomp E F w)) K₀)
        (θ : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ ⟶
          Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
        (_ : ∀ v : (↥L')ˣ, ((Additive.toMul (θ.hom (Additive.ofMul v)) : (w.adicCompletion F)ˣ) : w.adicCompletion F) = Φ.symm (v : L'))
        (u' : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ))
        (_ : ExtCitation.LocalLevel.IsLocalFundamentalClass q L' (↥(NumberField.PlaceDecomp.decomp E F w)) K₀ u'),
        ∀ (m a : ℕ) (_ : p.Coprime m) (_ : m * p ^ a = Nat.card ↥(NumberField.PlaceDecomp.decomp E F w)),
        m • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) (lam w) 2).hom
              ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) θ 2).hom u') =
          m • (groupCohomology.map (NumberField.PlaceDecomp.decomp E F w).subtype
              (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))) 2).hom uF) ∧
      (groupCohomology.map (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)) j 2).hom uF = Module.finrank F F' • uF' := by sorry
