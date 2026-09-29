-- Prove2me | Theorems.Thm_M4aHerbrand_exists_fundamentalClass_ideleClassGroup_res_eq_localFundamentalClass_of_isPGroup_of_ne_two
-- name    : M4aHerbrand.exists_fundamentalClass_ideleClassGroup_res_eq_localFundamentalClass_of_isPGroup_of_ne_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/a8a61eb0-9337-5ee0-96cd-464d3e938208
-- title:
--   Global fundamental class and its local components, odd p
-- statement:
--   Let $E \subseteq F$ be number fields with $F/E$ finite Galois, put $G = \mathrm{Gal}(F/E)$, and let $p$ be a prime with $p \neq 2$ such that $G$ is a $p$-group. Fix an idèle Galois descent datum $D$ for $F/E$, that is, a monoid homomorphism from $G$ to the ring automorphisms of the adèle ring of $F$ over $\mathcal{O}_F$, each automorphism continuous and compatible with the structure map of $F$; fix an action of $G$ by group automorphisms on the idèle class group $C_F = (\mathbb{A}_F)^\times/\,$(image of $F^\times$) that agrees with the action `D.classAct` induced by $D$. Fix, for each finite place $w$ of $F$ (a height-one prime of $\mathcal{O}_F$), a monoid homomorphism $\iota_w \colon (F_w)^\times \to (\mathbb{A}_F)^\times$ whose $w$-component is the identity, whose components at all $w' \neq w$ are $1$ and whose infinite part is $1$, and a morphism $\lambda_w$ of $\mathbb{Z}$-linear representations of the decomposition subgroup $D_w =$ `decomp E F w` $\le G$ from $(F_w)^\times$ to the restriction of $C_F$ along $D_w \hookrightarrow G$, given on elements by $x \mapsto [\iota_w(x)]$. Then there is a class $u \in H^2(G, C_F)$ such that: (i) for every subgroup $S \le G$, $H^1(S, C_F)$ is a zero object; (ii) for every finite subgroup $S \le G$, $\#H^2(S, C_F) = \#S$; (iii) for every subgroup $S \le G$ the restriction of $u$ to $H^2(S, C_F)$ spans it as a $\mathbb{Z}$-module; and (iv) for every finite place $w$ of $F$, every prime $q$, every finite extension $L'$ of $\mathbb{Q}_q$ inside a fixed algebraic closure carrying an action of $D_w$ by ring automorphisms and a compatible action on $(L')^\times$ fixing $\mathbb{Q}_q$ pointwise, every $D_w$-equivariant ring isomorphism $\Phi \colon F_w \to L'$, every finite extension $K_0$ of $\mathbb{Q}_q$ with $K_0 \le L'$ whose elements are exactly the $D_w$-fixed elements of $L'$, every representation morphism $\theta$ from $(L')^\times$ to $(F_w)^\times$ inducing $v \mapsto \Phi^{-1}(v)$, and every $u' \in H^2(D_w, (L')^\times)$ satisfying [`ExtCitation.LocalLevel.IsLocalFundamentalClass q L' D_w K₀`](def/ExtCitation_LocalLevel_FundamentalClass.html#L60) (the normalisation pinning $u'$ down, for each unramified overlay datum over $K_0$ with Frobenius lift and uniformiser, as the inflation of the class of the explicit carry cocycle), the image of $u'$ under $H^2(\theta)$ followed by $H^2(\lambda_w)$ equals the restriction of $u$ to $H^2(D_w, C_F)$.
--
--   This is the existence of the global fundamental class of the idèle class formation for a Galois $p$-extension of number fields with $p$ odd, together with Tate's reciprocity law identifying its restriction to each decomposition group with the image of the corresponding local fundamental class. It is used in the derivation of the global norm-index and Herbrand-quotient statements, in particular by [`M4aHerbrand.exists_span_eq_top_forall_map_inclusion_localFundamentalClass_eq_map_inclusion_of_isPGroup_of_ne_two`](thm.html#M4aHerbrand.exists_span_eq_top_forall_map_inclusion_localFundamentalClass_eq_map_inclusion_of_isPGroup_of_ne_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_exists_fundamentalClass_ideleClassGroup_res_eq_localFundamentalClass_of_isPGroup_of_ne_two.lean

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory NumberField IsDedekindDomain
open M4aHerbrand
open scoped NumberField.PlaceDecomp

theorem M4aHerbrand.exists_fundamentalClass_ideleClassGroup_res_eq_localFundamentalClass_of_isPGroup_of_ne_two
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hG : IsPGroup p (F ≃ₐ[E] F))
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
      (lam w).hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk (ι w x) : IdeleClassGroup (𝓞 F) F)) :
    ∃ u : groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2,
      (∀ S : Subgroup (F ≃ₐ[E] F), Limits.IsZero
        (groupCohomology (Rep.res S.subtype
          (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 1)) ∧
      (∀ (S : Subgroup (F ≃ₐ[E] F)) [Fintype S], Nat.card
        (groupCohomology (Rep.res S.subtype
          (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2) = Fintype.card S) ∧
      (∀ S : Subgroup (F ≃ₐ[E] F), Submodule.span ℤ
        {(groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype
          (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))) 2).hom u} = ⊤) ∧
      ∀ (w : HeightOneSpectrum (𝓞 F))
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
        (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) (lam w) 2).hom ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) θ 2).hom u') =
          (groupCohomology.map (NumberField.PlaceDecomp.decomp E F w).subtype
            (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))) 2).hom u := by sorry
