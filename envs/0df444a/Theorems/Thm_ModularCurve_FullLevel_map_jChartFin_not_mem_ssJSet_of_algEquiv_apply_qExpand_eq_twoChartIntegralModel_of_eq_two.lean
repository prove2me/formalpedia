-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_map_jChartFin_not_mem_ssJSet_of_algEquiv_apply_qExpand_eq_twoChartIntegralModel_of_eq_two
-- name    : ModularCurve.FullLevel.map_jChartFin_not_mem_ssJSet_of_algEquiv_apply_qExpand_eq_twoChartIntegralModel_of_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/320eb4a8-8bd5-5558-9057-b16843ca8391
-- title:
--   Non-supersingularity transports along an automorphism fixing j(q^q) (q=2)
-- statement:
--   Throughout, $\bar{\mathbb Q}$ denotes `AlgebraicClosure ℚ`, and the data are the following.
--
--   **Arithmetic data at $q$.** A prime $q$ with $q = 2$; a natural number $M' \neq 0$ with $q \nmid M'$; a valuation subring $A \subseteq \bar{\mathbb Q}$ lying over $q$ in the sense of `LiesOverPrime`, i.e. $q$ is a non-unit of $A$; a finite set $W$ of places of `modularFunctionFieldC (ResidueField A) M'` over the residue field of $A$ which, by `hW`, is exactly the set `ssPlaces q M' (ResidueField A)` of supersingular places (those places $w$ that are rational, are affine geometric places, and satisfy $w.\mathrm{evalAt}$ of the geometric $j$-generator lying in `ssJSet q (ResidueField A)`); the inclusion `hle` of `modularFunctionFieldBar M'` (the base change to $\bar{\mathbb Q}$ of the full level-$M'$ modular function field inside Laurent series) into `fieldBar q M'` $=$ `xHFunctionFieldBar (q ^ 2 * M') (levelH q M')`; a constant reduction $R_0$ of $A$ from `modularFunctionFieldBar M'` to `modularFunctionFieldC (ResidueField A) M'`, that is, a valuation subring $R_0.\mathrm{integers}$ with a surjective residue map onto `modularFunctionFieldC (ResidueField A) M'` whose kernel is the maximal ideal, compatible with $A$ and its residue map, satisfying the scaling property `exists_smul_mem`, together with a place map preserving degrees and compatible with divisors of functions; the hypothesis `hR₀`, which says that for every Laurent series $y$ with coefficients in $A$ whose image in $\bar{\mathbb Q}$ lies in `modularFunctionFieldBar M'`, that image lies in $R_0.\mathrm{integers}$ and its $R_0$-residue, read as a Laurent series over the residue field of $A$, is the coefficientwise reduction of $y$; and an index $\zeta$ in `Idx q`, i.e. a primitive $q$-th root of unity in $\bar{\mathbb Q}$.
--
--   **Two families of valuation subrings of `fieldBar q M'`.** A family $O_{\mathrm{Ig}}$ indexed by the projective line [`CuspidalType.ProjLine q`](def/CuspidalType_IsCuspidalOfType.html#L21) over $\mathbb Z/q$, and a family $O_{\mathrm{SS}}$ indexed by $W$.
--
--   *Igusa clauses.* `hIg_inf` describes $O_{\mathrm{Ig}}(\infty)$ at the line `lineInfty q`: an element $f$ belongs to it precisely when there are Laurent series $x, y$ with coefficients in $A$ such that the coefficientwise reduction of $y$ to the residue field of $A$ is non-zero and $f \cdot y = x$ as Laurent series over $\bar{\mathbb Q}$. `hIg` requires every line $\ell$ to be reached: there is $\gamma \in \Gamma_0(M')$ with `redQ q γ • lineInfty q = ℓ` and $O_{\mathrm{Ig}}(\ell)$ the pullback of $O_{\mathrm{Ig}}(\infty)$ along `levelAutBar q M' ζ γ`. `hIg_inj` asks that $O_{\mathrm{Ig}}$ be injective, and `hIg_perm` that for every index $\zeta'$ and every $\gamma \in \Gamma_0(M')$ the pullback along `levelAutBar q M' ζ' γ` permutes the family, i.e. equals $O_{\mathrm{Ig}} \circ \sigma$ for some permutation $\sigma$ of the projective line.
--
--   *Supersingular clauses.* `hSS_A` says that for each $s \in W$ and each $x \in \bar{\mathbb Q}$, the image of $x$ lies in $O_{\mathrm{SS}}(s)$ if and only if $x \in A$. `hSS_over` says that for $s \in W$ and $f \in R_0.\mathrm{integers}$ such that $f$ has non-negative order at every place of `modularFunctionFieldBar M'` over $\bar{\mathbb Q}$ at which the element $j$ (the coefficient embedding of the $q$-expansion `jq`, viewed in `modularFunctionFieldBar M'`) has non-negative order, and such that the $R_0$-residue of $f$ lies in the valuation subring of the place $s$, then the image of $f$ in `fieldBar q M'` lies in $O_{\mathrm{SS}}(s)$, and for every $a \in A$ whose residue equals $s.\mathrm{evalAt}$ of the $R_0$-residue of $f$, the difference between that image and $a$ lies in $O_{\mathrm{SS}}(s)$ and belongs to its maximal ideal. `hSS_fix` says each $O_{\mathrm{SS}}(s)$ is invariant under pullback along every `levelAutBar q M' ζ' γ` with $\gamma \in \Gamma_0(M')$. `hSS_tr` provides for each $s$ an element $t \in O_{\mathrm{SS}}(s)$ such that $t - a$ is a unit of $O_{\mathrm{SS}}(s)$ for every $a \in A$.
--
--   **Regular prolongation.** A regular prolongation $R$ of $A$ from `fieldBar q M'` to `xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')` (a valuation subring with surjective residue map whose kernel is the maximal ideal, compatible with $A$, and satisfying `exists_smul_mem`), with `hR` stating $R.\mathrm{integers} = O_{\mathrm{Ig}}(\infty)$, and `hR₀O` stating that $f$ lies in $R_0.\mathrm{integers}$ exactly when its image in `fieldBar q M'` lies in $O_{\mathrm{Ig}}(\infty)$.
--
--   **Uniformisers, a base field $k_0$, and an auxiliary prime $\ell$.** An element $\pi \in A$ with $\pi^{q^2-1} = q$; an intermediate field $k_0$ of $\bar{\mathbb Q}/\mathbb Q$ and $\pi_0 \in k_0$ lying in $A$ such that the contraction of $A$ to $k_0$ is a discrete valuation ring with maximal ideal generated by $\pi_0$, is Henselian, and has algebraically closed residue field, together with `hκ`: every $a \in A$ is congruent, modulo the maximal ideal of $A$, to an element of $k_0$ lying in $A$. Further, a prime $\ell$ with $\ell \geq 3$, $\ell \neq q$ and $\ell \nmid M'$; an element $\zeta_0 \in k_0$ which is a primitive $(q\ell)$-th root of unity in $\bar{\mathbb Q}$; and an element $\varpi_t \in k_0$ lying in $A$ with $\varpi_t^{q^2-1} = q\,u$ for some unit $u$ of $A$.
--
--   **A finite level field.** A finite extension $K_1$ of $k_0$ inside $\bar{\mathbb Q}$ and a valuation subring $A_1 \subseteq K_1$ whose elements are exactly those of $K_1$ lying in $A$, with $A_1$ a Henselian discrete valuation ring.
--
--   With `fieldBar q M'` regarded as a $k_0$-algebra through $\bar{\mathbb Q}$, the assertion is the following. Let $F_0$ be an intermediate field of `fieldBar q M'` over $k_0$ satisfying four conditions: the compositum of $F_0$ with the $k_0$-subfield generated by the image of $\bar{\mathbb Q}$ is all of `fieldBar q M'`; $F_0$ is stable under every `levelAutBar q M' ζ' γ` with $\gamma \in \Gamma_0(M')$; a linear disjointness condition, namely that for every finite extension $K'$ of $k_0$ in $\bar{\mathbb Q}$, every $m$, every $c : \mathrm{Fin}\,m \to \bar{\mathbb Q}$ linearly independent over $K'$ and every $a : \mathrm{Fin}\,m \to$ `fieldBar q M'` with all $a_i$ in the compositum of $F_0$ with the $k_0$-subfield generated by the image of $K'$, the relation $\sum_i c_i\, a_i = 0$ forces $a_i = 0$ for all $i$; and that every element of `fieldBar q M'` whose Laurent series has rational coefficients (lies in the range of `coeffEmb`) belongs to $F_0$.
--
--   Write $E$ for the compositum of $F_0$ with the $k_0$-subfield of `fieldBar q M'` generated by the image of $K_1$, and assume $E$ is an $A_1$-algebra whose structure map is the inclusion of $K_1$ into `fieldBar q M'` through $\bar{\mathbb Q}$. Let $j_1 \in E$ have image in `fieldBar q M'` equal to the inclusion of the element $j$ (the coefficient embedding of `jq`, viewed in `modularFunctionFieldBar M'`), and let $j_1 \neq 0$. Let $j' \in E$ have Laurent series equal to the coefficient embedding of `qExpand ℚ q jq`, the $q$-expansion of $j$ with all exponents multiplied by $q$.
--
--   Then the conclusion is: $j'$ lies in the chart algebra `chartAlgFin A₁ E j₁`, consisting of the elements of $E$ integral over the $A_1$-subalgebra generated by $j_1$; and for every $A_1$-algebra automorphism $\sigma$ of $E$ with $\sigma(j') = j'$ and such that for all $b \in E$ one has $b \in$ `chartAlgFin A₁ E j₁` if and only if $\sigma(b) \in$ `chartAlgFin A₁ E j₁`; and for all points $y, y'$ of the affine scheme `XFin A₁ E j₁` $=$ $\mathrm{Spec}$ of that chart algebra such that for every $b$ in the chart algebra with $\sigma^{-1}(b)$ again in the chart algebra one has $b \in y'$ if and only if $\sigma^{-1}(b) \in y$: if for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi$ from the chart algebra to $\Omega$ with kernel the prime of $y$ the value $\varphi(j_1)$ lies outside `ssJSet q Ω`, then for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi'$ from the chart algebra to $\Omega$ with kernel the prime of $y'$, the value $\varphi'(j_1)$ lies outside `ssJSet q Ω`. Here $j_1$ is taken as the element `jChartFin A₁ E j₁` of the chart algebra, and `ssJSet q Ω` is the set of those $j \in \Omega$ such that every elliptic Weierstrass curve over $\Omega$ with $j$-invariant $j$ has no non-trivial $q$-torsion affine point.
--
--   This is the $q = 2$ instance of the transport principle on the Igusa leg of the semistable covering of the full-level modular curve: the property of a point of the $j$-finite chart of the two-chart integral model not lying over a supersingular $j$-invariant is carried from a point $y$ to its image $y'$ under an automorphism of the level field fixing the $q$-fold $q$-expansion $j(\mathsf q^q)$ and stabilising the chart algebra. It feeds [`ModularCurve.FullLevel.exists_levelAutBar_smul_centred_twoChartIntegralModel_of_forall_not_ssTube_of_eq_two`](thm.html#ModularCurve.FullLevel.exists_levelAutBar_smul_centred_twoChartIntegralModel_of_forall_not_ssTube_of_eq_two), where charts centred away from the supersingular tubes are produced.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_map_jChartFin_not_mem_ssJSet_of_algEquiv_apply_qExpand_eq_twoChartIntegralModel_of_eq_two.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem ModularCurve.FullLevel.map_jChartFin_not_mem_ssJSet_of_algEquiv_apply_qExpand_eq_twoChartIntegralModel_of_eq_two
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (ζ : Idx q)
    (OIg : CuspidalType.ProjLine q → ValuationSubring (fieldBar q M'))
    (OSS : ↥W → ValuationSubring (fieldBar q M'))

    (hIg_inf : ∀ f : fieldBar q M', f ∈ OIg (lineInfty q) ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hIg : ∀ ℓ, ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ redQ q γ • lineInfty q = ℓ ∧
      OIg ℓ = (OIg (lineInfty q)).comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom)
    (hIg_inj : Function.Injective OIg)
    (hIg_perm : ∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      ∃ σ : Equiv.Perm (CuspidalType.ProjLine q),
        ∀ ℓ, (OIg ℓ).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OIg (σ ℓ))

    (hSS_A : ∀ s (x : AlgebraicClosure ℚ), algebraMap (AlgebraicClosure ℚ) (fieldBar q M') x ∈ OSS s ↔ x ∈ A)
    (hSS_over : ∀ (s : ↥W) (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
      (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
        (IntermediateField.inclusion hle f : fieldBar q M') ∈ OSS s ∧
        ∀ a : A, residue A a =
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
          ∃ h : (IntermediateField.inclusion hle f : fieldBar q M')
              - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s,
            (⟨_, h⟩ : OSS s) ∈ maximalIdeal (OSS s))
    (hSS_fix : ∀ (s : ↥W) (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      (OSS s).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OSS s)

    (hSS_tr : ∀ s : ↥W, ∃ t : fieldBar q M', t ∈ OSS s ∧ ∀ a : A,
      ∃ h : t - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s, IsUnit (⟨_, h⟩ : OSS s))
    (R : RegularProlongation A (fieldBar q M') (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))) (hR : R.integers = OIg (lineInfty q))
    (hR₀O : ∀ f : ↥(modularFunctionFieldBar M'), f ∈ R₀.integers ↔
      (IntermediateField.inclusion hle f : fieldBar q M') ∈ OIg (lineInfty q))

    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπP : π ∈ A)

    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ₀ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
      Ideal.span {(⟨π₀, hπ₀⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A)

    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (ζ₀ : ↥k₀) (hζ₀ : IsPrimitiveRoot ((ζ₀ : ↥k₀) : AlgebraicClosure ℚ) (q * ℓ))
    (ϖt : ↥k₀) (hϖtA : (ϖt : AlgebraicClosure ℚ) ∈ A)
    (hϖt : ∃ u : ↥A, IsUnit u ∧ (ϖt : AlgebraicClosure ℚ) ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ) * (u : AlgebraicClosure ℚ))

    (K₁ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (hK₁ : FiniteDimensional ↥k₀ ↥K₁)
    (A₁ : ValuationSubring ↥K₁) (hA₁ : ∀ x : ↥K₁, x ∈ A₁ ↔ (x : AlgebraicClosure ℚ) ∈ A)
    [IsDiscreteValuationRing ↥A₁] [HenselianLocalRing ↥A₁] :
    letI : Algebra ↥k₀ ↥(fieldBar q M') :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra

    ∀ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M')),
      (IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) ⊔ F₀ = ⊤) →
      (∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → ∀ f : ↥(fieldBar q M'), f ∈ F₀ → levelAutBar q M' ζ' γ f ∈ F₀) →
      (∀ (K' : IntermediateField ↥k₀ (AlgebraicClosure ℚ)), FiniteDimensional ↥k₀ ↥K' →
        ∀ (m : ℕ) (c : Fin m → AlgebraicClosure ℚ) (a : Fin m → ↥(fieldBar q M')), (∀ i, a i ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K' : Set (AlgebraicClosure ℚ))) ⊔ F₀) →
          LinearIndependent ↥K' c → ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c i) * a i = 0 → ∀ i, a i = 0) →
      (∀ f : ↥(fieldBar q M'), (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ Set.range ⇑(coeffEmb (AlgebraicClosure ℚ)) → f ∈ F₀) →

    ∀ [Algebra ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)],
      (∀ a : ↥A₁, ((algebraMap ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) a : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) =
        algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥K₁) : AlgebraicClosure ℚ)) →
    ∀ (j₁ : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)),
      ((j₁ : ↥(fieldBar q M')) = IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M'))) →
    ∀ [Fact (j₁ ≠ 0)],

    ∀ (j' : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)),
      ((j' : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq) →
      j' ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁ →
    ∀ (σ : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) ≃ₐ[↥A₁] ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)),
      σ j' = j' →
      (∀ b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀), b ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁ ↔ σ b ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) →

    ∀ (y y' : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁)),
      (∀ (b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁)) (hb : σ.symm (b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁),
          b ∈ y'.asIdeal ↔ (⟨σ.symm (b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)), hb⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁)) ∈ y.asIdeal) →

      (∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
          (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) →+* Ω), RingHom.ker φ = y.asIdeal →
            φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) ∉ ModularCurve.ssJSet q Ω) →
      ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
        (φ' : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) →+* Ω), RingHom.ker φ' = y'.asIdeal →
          φ' (AlgebraicCurve.TwoChartIntegralModel.jChartFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) ∉ ModularCurve.ssJSet q Ω := by sorry
