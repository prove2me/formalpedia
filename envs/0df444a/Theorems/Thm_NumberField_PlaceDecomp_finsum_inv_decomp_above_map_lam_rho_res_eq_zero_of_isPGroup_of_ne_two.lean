-- Prove2me | Theorems.Thm_NumberField_PlaceDecomp_finsum_inv_decomp_above_map_lam_rho_res_eq_zero_of_isPGroup_of_ne_two
-- name    : NumberField.PlaceDecomp.finsum_inv_decomp_above_map_lam_rho_res_eq_zero_of_isPGroup_of_ne_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/920916f0-8fcb-5f65-94a2-0a426b85c802
-- title:
--   Sum of local invariants of a global class vanishes
-- statement:
--   Let $F/E$ be a Galois extension of number fields with group $G=\mathrm{Gal}(F/E)$, let $p$ be a prime with $p \neq 2$, and assume $G$ is a $p$-group. Let $D$ be a Galois descent datum for the adèles of $F$, i.e. a homomorphism from $G$ to the ring automorphisms of $\mathrm{AdeleRing}(\mathcal{O}_F,F)$ that is continuous and compatible with the diagonal map from $F$; let the given action of $G$ on the idèle class group $C_F=(\mathrm{AdeleRing}(\mathcal{O}_F,F))^\times/\mathrm{im}(F^\times)$ be the one induced by $D$. Further data: maps $\iota_w\colon F_w^\times \to \mathbb{I}_F^\times$ placing a local unit in the coordinate at $w$ with all other finite coordinates and the infinite coordinate equal to $1$; morphisms $\lambda_w$ of representations of the decomposition subgroup $D_w \le G$ of the valuation of $w$, from the multiplicative group $F_w^\times$ (written additively) to the restriction to $D_w$ of $C_F$, given on points by $x \mapsto [\iota_w(x)]$; a class $x \in H^2(G,F^\times)$; morphisms $\rho_w$ from the restriction of $F^\times$ to $D_w$ into $F_w^\times$, given on points by the diagonal embedding $F \to F_w$. Finally, invariant maps $\mathrm{inv}_G\colon H^2(G,C_F) \to \mathbb{Q}/\mathbb{Z}$ and, for each subgroup $H \le G$, $\mathrm{inv}_H\colon H^2(H,C_F) \to \mathbb{Q}/\mathbb{Z}$ (the target being $\mathrm{AddCircle}\,(1:\mathbb{Q})$), subject to: both are injective; the image of $\mathrm{inv}_G$ is the $|G|$-torsion and that of $\mathrm{inv}_H$ the $|H|$-torsion; $\mathrm{inv}_H \circ \mathrm{res}_H = [G:H]\cdot \mathrm{inv}_G$; $\mathrm{inv}_G$ agrees with $\mathrm{inv}_\top$ after restriction to the full subgroup; and a local normalisation: whenever a finite place $w$ is presented through a ring isomorphism $\Phi\colon F_w \cong L'$ with $L'$ a finite extension of $\mathbb{Q}_q$ inside a fixed algebraic closure, $D_w$ acting $\mathbb{Q}_q$-semilinearly on $L'$ compatibly with $\Phi$ and with the action on units, $K_0$ a finite extension of $\mathbb{Q}_q$ contained in $L'$ whose elements are exactly the $D_w$-fixed points of $L'$, $\theta$ the morphism of $D_w$-representations $(L')^\times \to F_w^\times$ induced by $\Phi^{-1}$, and $u' \in H^2(D_w,(L')^\times)$ a local fundamental class in the sense of the predicate [`ExtCitation.LocalLevel.IsLocalFundamentalClass`](def/ExtCitation_LocalLevel_FundamentalClass.html#L60) (which pins $u'$ down, for every unramified overlay datum with distinguished Frobenius lift and uniformiser, as the inflation of the class of the associated cyclic carry cocycle), one has $\mathrm{inv}_{D_w}(\lambda_{w,*}\theta_* u') = 1/|D_w|$. Let $S$ be a finite set of rational primes and assume that for every finite place $w$ of $F$ at which no prime of $S$ lies (no $q \in S$ has image in $w$) the local component $\rho_{w,*}\,\mathrm{res}_{D_w}\,x$ vanishes in $H^2(D_w,F_w^\times)$. Then, writing $w(v)$ for the chosen place of $F$ above a finite place $v$ of $E$, the finite sum over all finite places $v$ of $E$ of $\mathrm{inv}_{D_{w(v)}}\bigl(\lambda_{w(v),*}\,\rho_{w(v),*}\,\mathrm{res}_{D_{w(v)}}\,x\bigr)$ is $0$ in $\mathbb{Q}/\mathbb{Z}$.
--
--   This is the reciprocity law of global class field theory for the layer $F/E$, expressed in the currency of the abstract invariant maps: the local invariants of a class coming from $H^2(G,F^\times)$ sum to zero, the sum being finite because the class is unramified outside the places above $S$. It feeds into [`NumberField.PlaceDecomp.sum_sum_inv_decomp_eq_zero_of_forall_inv_eq_of_isUnramifiedOutside`](thm.html#NumberField.PlaceDecomp.sum_sum_inv_decomp_eq_zero_of_forall_inv_eq_of_isUnramifiedOutside), where the places of $E$ are grouped according to the primes of $S$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceDecomp_finsum_inv_decomp_above_map_lam_rho_res_eq_zero_of_isPGroup_of_ne_two.lean

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 400000
open CategoryTheory groupCohomology NumberField IsDedekindDomain
open M4aHerbrand
open scoped NumberField.PlaceDecomp

theorem NumberField.PlaceDecomp.finsum_inv_decomp_above_map_lam_rho_res_eq_zero_of_isPGroup_of_ne_two
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hG : IsPGroup p (F ≃ₐ[E] F))
    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (hact : ∀ (g : (F ≃ₐ[E] F)) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c)
    (ι : ∀ w : HeightOneSpectrum (𝓞 F), (w.adicCompletion F)ˣ →* (AdeleRing (𝓞 F) F)ˣ)
    (hι : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ),
      finPart w (ι w x) = x ∧ (∀ w' : HeightOneSpectrum (𝓞 F), w' ≠ w → finPart w' (ι w x) = 1) ∧ infPart (ι w x) = 1)
    (lam : ∀ w : HeightOneSpectrum (𝓞 F),
      Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (w.adicCompletion F)ˣ ⟶
        Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))
    (hlam : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ),
      (lam w).hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk (ι w x) : IdeleClassGroup (𝓞 F) F))
    (x : groupCohomology.H2 (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ))
    (ρ : ∀ w : HeightOneSpectrum (𝓞 F),
      Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ) ⟶
        Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (w.adicCompletion F)ˣ)
    (hρ : ∀ (w : HeightOneSpectrum (𝓞 F)) (u : Fˣ),
      (ρ w).hom (Additive.ofMul u) = Additive.ofMul (Units.map (algebraMap F (w.adicCompletion F)).toMonoidHom u))

    (invG : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2) →+ AddCircle (1 : ℚ))
    (inv : ∀ H : Subgroup (F ≃ₐ[E] F),
      ↥(groupCohomology (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2) →+ AddCircle (1 : ℚ))
    (_ : Function.Injective invG)
    (_ : ∀ H : Subgroup (F ≃ₐ[E] F), Function.Injective (inv H))
    (_ : ∀ t : AddCircle (1 : ℚ), t ∈ invG.range ↔ Nat.card (F ≃ₐ[E] F) • t = 0)
    (_ : ∀ (H : Subgroup (F ≃ₐ[E] F)) (t : AddCircle (1 : ℚ)), t ∈ (inv H).range ↔ Nat.card ↥H • t = 0)
    (_ : ∀ (H : Subgroup (F ≃ₐ[E] F)) (y : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2)),
      inv H ((groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))) 2).hom y) =
        H.index • invG y)
    (_ : ∀ (w : HeightOneSpectrum (𝓞 F))
        (q : ℕ) [Fact q.Prime] (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L']
        [MulSemiringAction ↥(NumberField.PlaceDecomp.decomp E F w) L'] [MulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (↥L')ˣ]
        (Φ : w.adicCompletion F ≃+* L')
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (x : ℚ_[q]), g • algebraMap ℚ_[q] L' x = algebraMap ℚ_[q] L' x)
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (v : (↥L')ˣ), ((g • v : (↥L')ˣ) : L') = g • (v : L'))
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (x : w.adicCompletion F), Φ (g • x) = g • Φ x)
        (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀]
        (_ : ExtCitation.LocalLevel.IsBase q L' ↥(NumberField.PlaceDecomp.decomp E F w) K₀)
        (θ : Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (↥L')ˣ ⟶ Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (w.adicCompletion F)ˣ)
        (_ : ∀ v : (↥L')ˣ, ((Additive.toMul (θ.hom (Additive.ofMul v)) : (w.adicCompletion F)ˣ) : w.adicCompletion F) = Φ.symm (v : L'))
        (u' : groupCohomology.H2 (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (↥L')ˣ))
        (_ : ExtCitation.LocalLevel.IsLocalFundamentalClass q L' ↥(NumberField.PlaceDecomp.decomp E F w) K₀ u'),
        inv (NumberField.PlaceDecomp.decomp E F w)
            ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) (lam w) 2).hom
              ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) θ 2).hom u')) =
          (((1 : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) : ℚ) : ℚ) : AddCircle (1 : ℚ)))
    (_ : ∀ y : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2),
        invG y = inv ⊤ ((groupCohomology.map (⊤ : Subgroup (F ≃ₐ[E] F)).subtype
          (𝟙 (Rep.res (⊤ : Subgroup (F ≃ₐ[E] F)).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))) 2).hom y))

    (S : Finset Nat.Primes)
    (hoff : ∀ w : HeightOneSpectrum (𝓞 F), (∀ q : ↥S, (((q : Nat.Primes) : ℕ) : 𝓞 F) ∉ w.asIdeal) →
      (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) (ρ w) 2).hom
        ((groupCohomology.map (NumberField.PlaceDecomp.decomp E F w).subtype
          (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ))) 2).hom x) = 0) :
    ∑ᶠ v : HeightOneSpectrum (𝓞 E),
      inv (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))
        ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (lam (NumberField.PlaceAbove.above E F v)) 2).hom
          ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (ρ (NumberField.PlaceAbove.above E F v)) 2).hom
            ((groupCohomology.map (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)).subtype
              (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ))) 2).hom x))) = 0 := by sorry
