-- Prove2me | Theorems.Thm_M4aHerbrand_exists_unit_forall_exists_localFundamentalClass_eq_smul_res_and_pow_dvd_of_forall_map_inclusion_eq
-- name    : M4aHerbrand.exists_unit_forall_exists_localFundamentalClass_eq_smul_res_and_pow_dvd_of_forall_map_inclusion_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/c01e0608-34a8-58ce-9847-c944f03ee23c
-- title:
--   A p-adic comparison constant for local fundamental classes
-- statement:
--   Fix an odd prime $p$ and a Galois extension $E \subseteq F$ of number fields with group $G = \mathrm{Gal}(F/E)$, and write $C_F = (\mathbb{A}_F)^{\times}/F^{\times}$ for the quotient of the units of the adele ring of $\mathcal{O}_F$ by the image of $F^{\times}$. The data are: a descent datum $D$, i.e. a homomorphism from $G$ to the ring automorphisms of $\mathbb{A}_F$ that is continuous and compatible with $F \to \mathbb{A}_F$; a multiplicative distributive action of $G$ on $C_F$ agreeing with the induced action `D.classAct`; for each finite place $w$ a homomorphism $\iota_w$ from $(F_w)^{\times}$ to $(\mathbb{A}_F)^{\times}$ whose component at $w$ is the identity and whose other finite and infinite components are $1$; and for each $w$ a morphism $\lambda_w$ of representations of the decomposition subgroup $D_w$ (the decomposition subgroup of the valuation subring of $w$) from $(F_w)^{\times}$ to the restriction of $C_F$, inducing $x \mapsto [\iota_w x]$. Further data: a class $u_0 \in H^2(G, C_F)$ such that $\#H^2(S, C_F) = \#S$ for every finite subgroup $S \le G$ and the restriction of $u_0$ to any subgroup $S$ spans $H^2(S,C_F)$ over $\mathbb{Z}$; a $p$-subgroup $P \le G$ of index prime to $p$; and a class $u_P \in H^2(P, C_F)$ spanning $H^2(P,C_F)$ over $\mathbb{Z}$. The local hypothesis is: for every finite place $w$, every prime $q$, every finite extension $L'/\mathbb{Q}_q$ inside a fixed algebraic closure carrying a $D_w$-action on $L'$ and on $(L')^{\times}$, every ring isomorphism $\Phi : F_w \cong L'$ that is $D_w$-equivariant, with $D_w$ acting $\mathbb{Q}_q$-linearly and compatibly on units, every finite $K_0/\mathbb{Q}_q$ with $K_0 \le L'$ and $K_0$ cut out in $L'$ exactly by the $D_w$-fixed points, every morphism $\theta$ of $D_w$-representations $(L')^{\times} \to (F_w)^{\times}$ underlain by $\Phi^{-1}$, and every $u' \in H^2(D_w, (L')^{\times})$ satisfying [`ExtCitation.LocalLevel.IsLocalFundamentalClass`](def/ExtCitation_LocalLevel_FundamentalClass.html#L60) for these data, the restriction to $D_w \cap P$ of $H^2(\lambda_w)(H^2(\theta)u')$ equals the restriction of $u_P$ to $D_w \cap P$. The conclusion asserts the existence of an integer $a$ with $p \nmid a$ such that for all $w$ and all such $q, L', \Phi, K_0, \theta, u'$ there is an integer $c$ with $H^2(\lambda_w)(H^2(\theta)u') = c \cdot \mathrm{res}_{D_w} u_0$ in $H^2(D_w, C_F)$ and $p^n \mid c a - 1$ whenever $p^n \mid \#D_w$.
--
--   This is the step passing from a normalised generator of $H^2$ over a Sylow $p$-subgroup, whose restrictions match the local fundamental classes, to a single comparison constant measuring the image of each local fundamental class against the restriction of a fixed global class $u_0$, congruent to the inverse of a $p$-adic unit $a$ modulo the local degrees. It feeds the odd-prime case [`M4aHerbrand.exists_unit_forall_exists_localFundamentalClass_eq_smul_res_and_pow_dvd_of_ne_two`](thm.html#M4aHerbrand.exists_unit_forall_exists_localFundamentalClass_eq_smul_res_and_pow_dvd_of_ne_two) in the construction of the global fundamental class of $F/E$, the arguments used being conjugation invariance of $H^2(G,C_F)$ and transport of local fundamental classes along conjugation of places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_exists_unit_forall_exists_localFundamentalClass_eq_smul_res_and_pow_dvd_of_forall_map_inclusion_eq.lean

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory NumberField IsDedekindDomain M4aHerbrand
open scoped NumberField.PlaceDecomp

theorem M4aHerbrand.exists_unit_forall_exists_localFundamentalClass_eq_smul_res_and_pow_dvd_of_forall_map_inclusion_eq
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
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
    (u₀ : groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2)
    (h2 : ∀ (S : Subgroup (F ≃ₐ[E] F)) [Fintype S], Nat.card
        (groupCohomology (Rep.res S.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2) = Fintype.card S)
    (h3 : ∀ S : Subgroup (F ≃ₐ[E] F), Submodule.span ℤ
        {(groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))) 2).hom u₀} = ⊤)
    (P : Subgroup (F ≃ₐ[E] F)) (hP : IsPGroup p P) (hPidx : ¬ p ∣ P.index)
    (uP : groupCohomology (Rep.res P.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2) (hspan : Submodule.span ℤ {uP} = ⊤)
    (hloc :
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
        ((groupCohomology.map (Subgroup.inclusion (inf_le_left : (NumberField.PlaceDecomp.decomp E F w) ⊓ P ≤ (NumberField.PlaceDecomp.decomp E F w)))
            (𝟙 (Rep.res (Subgroup.inclusion (inf_le_left : (NumberField.PlaceDecomp.decomp E F w) ⊓ P ≤ (NumberField.PlaceDecomp.decomp E F w))) (Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))))) 2).hom
          ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) (lam w) 2).hom ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) θ 2).hom u')) : groupCohomology (Rep.res ((NumberField.PlaceDecomp.decomp E F w) ⊓ P).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2) =
        ((groupCohomology.map (Subgroup.inclusion (inf_le_right : (NumberField.PlaceDecomp.decomp E F w) ⊓ P ≤ P))
            (𝟙 (Rep.res (Subgroup.inclusion (inf_le_right : (NumberField.PlaceDecomp.decomp E F w) ⊓ P ≤ P)) (Rep.res P.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))))) 2).hom
          uP : groupCohomology (Rep.res ((NumberField.PlaceDecomp.decomp E F w) ⊓ P).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2)) :
    ∃ a : ℤ, ¬ (p : ℤ) ∣ a ∧
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
        ∃ c : ℤ, ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) (lam w) 2).hom ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) θ 2).hom u')) = c • ((groupCohomology.map (NumberField.PlaceDecomp.decomp E F w).subtype (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))) 2).hom u₀) ∧
          ∀ n : ℕ, p ^ n ∣ Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) → (p : ℤ) ^ n ∣ c * a - 1 := by sorry
