-- Prove2me | Theorems.Thm_M4aHerbrand_exists_unit_forall_exists_localFundamentalClass_eq_smul_res_and_pow_dvd_of_ne_two
-- name    : M4aHerbrand.exists_unit_forall_exists_localFundamentalClass_eq_smul_res_and_pow_dvd_of_ne_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/826114f2-168f-563a-bff3-dc2ab04c6501
-- title:
--   A p-adic comparison constant for the local fundamental classes
-- statement:
--   Let $p$ be an odd prime and $F/E$ a finite Galois extension of number fields, with $G=\operatorname{Gal}(F/E)$ acting on the idèle class group $C_F=(\mathbb{A}_F)^\times/F^\times$ through a descent datum $D$ (a continuous action on $\mathbb{A}_F$ by ring automorphisms compatible with the embedding of $F$), the given `MulDistribMulAction` of $G$ on $C_F$ agreeing with $D$'s induced action. For each finite place $w$ of $F$ one is given a monoid map $\iota_w\colon (F_w)^\times\to(\mathbb{A}_F)^\times$ which is the identity in the $w$-component and trivial in all other finite components and at infinity, and a morphism $\lambda_w$ of $\mathbb{Z}$-representations of the decomposition group $D_w$ from $(F_w)^\times$ to the restriction of $C_F$, inducing $x\mapsto[\iota_w(x)]$. Let $u_0\in H^2(G,C_F)$ be such that $\#H^2(S,C_F)=\#S$ and $\mathbb{Z}\cdot\operatorname{res}_S u_0=H^2(S,C_F)$ for every subgroup $S\le G$. Then there is an integer $a$ prime to $p$ such that for every finite place $w$, every prime $q$, every finite extension $L'$ of $\mathbb{Q}_q$ inside the fixed algebraic closure carrying a $D_w$-action, every $D_w$-equivariant ring isomorphism $\Phi\colon F_w\to L'$ fixing $\mathbb{Q}_q$ and compatible with the unit action, every finite $K_0$ with $K_0\le L'$ and $K_0=(L')^{D_w}$, every units-transport morphism $\theta$ induced by $\Phi^{-1}$, and every $u'\in H^2(D_w,(L')^\times)$ satisfying the predicate [`ExtCitation.LocalLevel.IsLocalFundamentalClass`](def/ExtCitation_LocalLevel_FundamentalClass.html#L60) for $(q,L',D_w,K_0)$, there is $c\in\mathbb{Z}$ with $H^2(\lambda_w)\bigl(H^2(\theta)u'\bigr)=c\cdot\operatorname{res}_{D_w}u_0$ and $p^n\mid \#D_w \Rightarrow p^n\mid ca-1$ for all $n$.
--
--   This is the $p$-part of the local–global compatibility of the global fundamental class, in a normalisation-free form: the single constant $a$ measures how the chosen generator $u_0$ of $H^2(G,C_F)$ differs from the canonical class, uniformly in the place $w$ and in the chosen $q$-adic presentation of $F_w$. The quantifier order $\exists a\,\forall w\,\forall(\text{presentation})\,\exists c$ is what is used downstream, where the compatible family of local constants is assembled into a statement about the global fundamental class.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_exists_unit_forall_exists_localFundamentalClass_eq_smul_res_and_pow_dvd_of_ne_two.lean

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

theorem M4aHerbrand.exists_unit_forall_exists_localFundamentalClass_eq_smul_res_and_pow_dvd_of_ne_two
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
        {(groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))) 2).hom u₀} = ⊤) :
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
