-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_forall_coe_mem_igusa_iff_of_valuationSubring_levelField_of_eq_three
-- name    : ModularCurve.FullLevel.exists_forall_coe_mem_igusa_iff_of_valuationSubring_levelField_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/4b441011-5f9a-5ed1-94b5-71d99adbfb58
-- title:
--   Branches of the level-field model are Igusa rings (q=3)
-- statement:
--   Throughout, $q$ is a prime with $q = 3$, and $M'$ is a nonzero natural number with $q \nmid M'$. Fix a valuation subring $A$ of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` with `A.LiesOverPrime q`, i.e. $q$ lies in `A.nonunits`. Write $\mathcal{F} =$ `modularFunctionFieldBar M'` for the intermediate field of `LaurentSeries (AlgebraicClosure ℚ)` over $\overline{\mathbb{Q}}$ obtained by base change of the full level-$M'$ function field, and $\mathcal{F}_{\mathrm{bar}} =$ `fieldBar q M'` $=$ `xHFunctionFieldBar (q ^ 2 * M') (levelH q M')`, the analogous base-changed field for the level $q^2M'$ and the subgroup `levelH q M'` of $(\mathbb{Z}/q^2M')^\times$ (the kernel of reduction to $(\mathbb{Z}/q)^\times$); the hypothesis `hle` asserts $\mathcal{F} \le \mathcal{F}_{\mathrm{bar}}$.
--
--   The *characteristic-$p$ reduction data* consist of: a finite set $W$ of places of `modularFunctionFieldC (ResidueField A) M'` over the residue field of $A$, with `hW` saying that $W$ is exactly `ssPlaces q M' (ResidueField A)`, the set of places $w$ that are rational, are affine geometric places, and satisfy $w.\mathrm{evalAt}(\mathtt{jGeomGen}) \in \mathtt{ssJSet } q$; a constant reduction $R_0$ of $\mathcal{F}$ along $A$ with values in `modularFunctionFieldC (ResidueField A) M'`, that is, a valuation subring `R₀.integers` of $\mathcal{F}$ whose intersection with $\overline{\mathbb{Q}}$ is $A$, together with a surjective residue homomorphism onto the characteristic-$p$ modular function field whose kernel is the maximal ideal, compatible with the residue map of $A$, with the rescaling property `exists_smul_mem`, and with a map on places preserving degrees and compatible with divisor pushforward; and the hypothesis `hR₀`, that for every Laurent series $y$ with coefficients in $A$ whose image in `LaurentSeries (AlgebraicClosure ℚ)` lies in $\mathcal{F}$, this image lies in `R₀.integers` and its $R_0$-residue, read as a Laurent series over the residue field of $A$, is the coefficientwise reduction of $y$. An element $\zeta$ of `Idx q`, i.e. a primitive $q$-th root of unity in $\overline{\mathbb{Q}}$, is fixed.
--
--   The *two families of valuation subrings of* $\mathcal{F}_{\mathrm{bar}}$ are $O^{\mathrm{Ig}} =$ `OIg`, indexed by the projective line $\mathbb{P}^1(\mathbb{Z}/q)$ ([`CuspidalType.ProjLine q`](def/CuspidalType_IsCuspidalOfType.html#L21)), and $O^{\mathrm{SS}} =$ `OSS`, indexed by $W$. Their hypotheses are: `hIg_inf`, that $f \in O^{\mathrm{Ig}}(\mathtt{lineInfty } q)$ (with `lineInfty q` the point $[1:0]$) holds precisely when $f \cdot \bar{y} = \bar{x}$ for some Laurent series $x, y$ with coefficients in $A$ whose coefficientwise reductions satisfy $\bar y \ne 0$; `hIg`, that each index $\ell$ is reached from $[1:0]$ by the mod-$q$ reduction `redQ q γ` of some $\gamma \in \Gamma_0(M')$, with $O^{\mathrm{Ig}}(\ell)$ the pullback of $O^{\mathrm{Ig}}([1:0])$ along the automorphism `levelAutBar q M' ζ γ` of $\mathcal{F}_{\mathrm{bar}}$ (the $\overline{\mathbb{Q}}$-automorphism selected by the predicate `IsLevelAutBar` for the pair $(\zeta,\gamma)$, and the identity if none exists); `hIg_inj`, injectivity of $O^{\mathrm{Ig}}$; and `hIg_perm`, that for every $\zeta'$ and every $\gamma \in \Gamma_0(M')$ pullback along `levelAutBar q M' ζ' γ` permutes the family $O^{\mathrm{Ig}}$. For $O^{\mathrm{SS}}$: `hSS_A` says that a constant $x \in \overline{\mathbb{Q}}$ lies in $O^{\mathrm{SS}}(s)$ iff $x \in A$; `hSS_over` says that for $s \in W$ and $f \in$ `R₀.integers` which has non-negative order at every place of $\mathcal{F}$ over $\overline{\mathbb{Q}}$ at which the base-changed $q$-expansion `jq` of the modular invariant has non-negative order, and whose $R_0$-residue lies in the valuation subring of the place $s$, the image of $f$ in $\mathcal{F}_{\mathrm{bar}}$ lies in $O^{\mathrm{SS}}(s)$, and for every $a \in A$ with $\mathrm{residue}_A(a) = s.\mathrm{evalAt}(R_0.\mathrm{residue}(f))$ the difference of that image and $a$ lies in the maximal ideal of $O^{\mathrm{SS}}(s)$; `hSS_fix` says each $O^{\mathrm{SS}}(s)$ is invariant under pullback along every `levelAutBar q M' ζ' γ` with $\gamma \in \Gamma_0(M')$; `hSS_tr` provides for each $s$ an element $t \in O^{\mathrm{SS}}(s)$ such that $t - a$ is a unit of $O^{\mathrm{SS}}(s)$ for every $a \in A$. Finally $R$ is a regular prolongation of $A$ on $\mathcal{F}_{\mathrm{bar}}$ with residue field `xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')` — a valuation subring with surjective residue map of kernel the maximal ideal, lying over $A$ and compatible with its residue map, plus the rescaling property — subject to `hR` : `R.integers` $= O^{\mathrm{Ig}}([1:0])$, and `hR₀O` says that $f \in$ `R₀.integers` holds iff the image of $f$ in $\mathcal{F}_{\mathrm{bar}}$ lies in $O^{\mathrm{Ig}}([1:0])$.
--
--   The *arithmetic data* are: an element $\pi \in A$ with $\pi^{q^2-1} = q$; an intermediate field $k_0$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ and an element $\pi_0 \in k_0$ lying in $A$, such that the valuation subring $A \cap k_0$ is a discrete valuation ring with maximal ideal generated by $\pi_0$, is henselian, and has algebraically closed residue field, together with `hκ`: every $a \in A$ is congruent modulo the maximal ideal of $A$ to some element of $k_0$ lying in $A$; a prime $\ell \geq 3$ with $\ell \neq q$ and $\ell \nmid M'$, an element $\zeta_0 \in k_0$ which is a primitive $q\ell$-th root of unity, and an element $\varpi_t \in k_0 \cap A$ with $\varpi_t^{q^2-1} = q u$ for some unit $u$ of $A$; and one finite layer: an intermediate field $K_1$ of $\overline{\mathbb{Q}}/k_0$, finite-dimensional over $k_0$, with a valuation subring $A_1$ of $K_1$ cut out by $A$ (i.e. $x \in A_1 \iff x \in A$), which is a discrete valuation ring and henselian.
--
--   The conclusion is stated for $\mathcal{F}_{\mathrm{bar}}$ regarded as a $k_0$-algebra through $\overline{\mathbb{Q}}$. It asserts: for every intermediate field $F_0$ of $\mathcal{F}_{\mathrm{bar}}/k_0$ such that (i) the compositum of $F_0$ with the $k_0$-subfield generated by the image of $\overline{\mathbb{Q}}$ is all of $\mathcal{F}_{\mathrm{bar}}$, (ii) $F_0$ is stable under `levelAutBar q M' ζ' γ` for all $\zeta'$ and all $\gamma \in \Gamma_0(M')$, (iii) for every finite extension $K'$ of $k_0$ inside $\overline{\mathbb{Q}}$, every $m$, every $c : \mathrm{Fin}\,m \to \overline{\mathbb{Q}}$ linearly independent over $K'$ and every $a : \mathrm{Fin}\,m \to \mathcal{F}_{\mathrm{bar}}$ with all $a_i$ in the compositum of $F_0$ with the $k_0$-subfield generated by the image of $K'$, the relation $\sum_i c_i a_i = 0$ forces $a_i = 0$ for all $i$, and (iv) every element of $\mathcal{F}_{\mathrm{bar}}$ whose underlying Laurent series has rational coefficients (lies in the range of `coeffEmb (AlgebraicClosure ℚ)`) belongs to $F_0$ — then, writing $T_1$ for the compositum of $F_0$ with the $k_0$-subfield of $\mathcal{F}_{\mathrm{bar}}$ generated by the image of $K_1$, the following holds for every $A_1$-algebra structure on $T_1$ whose structure map sends $a \in A_1$ to the image of $a$ under $\overline{\mathbb{Q}} \to \mathcal{F}_{\mathrm{bar}}$, for every $j_1 \in T_1$ whose image in $\mathcal{F}_{\mathrm{bar}}$ is the element of $\mathcal{F}$ given by the coefficientwise base change of `jq` (and with $j_1 \neq 0$), for every uniformiser $\varpi$ of $A_1$ (i.e. maximal ideal of $A_1$ equal to the span of $\varpi$), and for every valuation subring $V$ of $T_1$ such that the image of $A_1$ is contained in $V$, the image of $\varpi$ lies in `V.nonunits`, and for every polynomial $P \in A_1[X]$ not divisible by $\varpi$ both $P(j_1)$ and $P(j_1)^{-1}$ lie in $V$: there exists a point of the projective line $\mathbb{P}^1(\mathbb{Z}/q)$ (the binder in the conclusion reuses the name `ℓ`) such that for every $f \in T_1$ one has $f \in V$ if and only if the image of $f$ in $\mathcal{F}_{\mathrm{bar}}$ lies in $O^{\mathrm{Ig}}$ at that point.
--
--   This is the branch-identification step for the Igusa tower at $q = 3$: any valuation subring of the level-field model $T_1 = K_1 \cdot F_0$ that dominates $A_1$, has $\varpi$ as a non-unit and makes every $\varpi$-primitive polynomial in $j_1$ invertible is the trace of one of the Igusa valuation rings $O^{\mathrm{Ig}}_\ell$, indexed by $\mathbb{P}^1(\mathbb{Z}/q)$; it is the exact twin, with $q = 3$ in place of $q \geq 5$, of the corresponding statement for larger $q$. It is used downstream in the analysis of the special fibre of the semistable covering of the full-level modular curve, in particular by the statements identifying maximal ideals of the chart algebras and the rational places attached to them.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_forall_coe_mem_igusa_iff_of_valuationSubring_levelField_of_eq_three.lean

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

theorem ModularCurve.FullLevel.exists_forall_coe_mem_igusa_iff_of_valuationSubring_levelField_of_eq_three
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
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

    ∀ (ϖ : ↥A₁), IsLocalRing.maximalIdeal ↥A₁ = Ideal.span {ϖ} →
    ∀ (V : ValuationSubring ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)),
      (∀ a : ↥A₁, algebraMap ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) a ∈ V) →
      algebraMap ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) ϖ ∈ V.nonunits →
      (∀ P : Polynomial ↥A₁, ¬ (Polynomial.C ϖ ∣ P) →
        Polynomial.aeval j₁ P ∈ V ∧ (Polynomial.aeval j₁ P)⁻¹ ∈ V) →
      ∃ ℓ : CuspidalType.ProjLine q, ∀ f : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀), f ∈ V ↔ ((f : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ OIg ℓ := by sorry
