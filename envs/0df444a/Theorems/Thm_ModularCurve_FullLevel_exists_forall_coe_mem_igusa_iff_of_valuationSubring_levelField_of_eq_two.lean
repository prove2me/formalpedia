-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_forall_coe_mem_igusa_iff_of_valuationSubring_levelField_of_eq_two
-- name    : ModularCurve.FullLevel.exists_forall_coe_mem_igusa_iff_of_valuationSubring_levelField_of_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/cd695140-d736-503e-9b1b-94bc9b92bcee
-- title:
--   Branch identification in the Igusa tower at q=2
-- statement:
--   Throughout, $q$ is a prime with $q = 2$, $M'$ is a nonzero natural number with $q \nmid M'$, and $A$ is a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` with `A.LiesOverPrime q`, i.e. $q$ is a non-unit of $A$. Write $k_A =$ `ResidueField A`. Two function fields occur: `modularFunctionFieldBar M'`, the intermediate field of `LaurentSeries (AlgebraicClosure ℚ)` obtained by adjoining to $\overline{\mathbb{Q}}$ the coefficientwise image under `coeffEmb` of `modularFunctionFieldFull M'` (itself $\mathbb{Q}$ adjoin the divisor expansions at level $M'$); and `fieldBar q M'` $=$ `xHFunctionFieldBar (q ^ 2 * M') (levelH q M')`, the analogous base change of the $X_H$-function field of level $q^2M'$ for $H =$ `levelH q M'`, the kernel of the reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$ (the units congruent to $1$ modulo $q$). The hypothesis `hle` asserts the first field is contained in the second. Further, $W$ is a finite set of places of `modularFunctionFieldC k_A M'` over $k_A$ (a `Place K F` being a valuation subring of $F$ containing the image of $K$, proper, with principal ideals; `modularFunctionFieldC K N` is $K$ adjoin the two $q$-expansions `jqModC K` and `jqNModC K N`), and `hW` says that $W$ consists exactly of the members of `ssPlaces q M' k_A`, i.e. of the places $w$ that are rational, satisfy `IsAffineGeomPlace k_A M' w`, and for which $w$`.evalAt (jGeomGen k_A M')` lies in `ssJSet q k_A`.
--
--   The reduction datum is a `ConstantReduction A` of `modularFunctionFieldBar M'` with values in `modularFunctionFieldC k_A M'`, called $R_0$: a valuation subring `R₀.integers` of the source, a surjective ring map `R₀.residue` to the target with kernel the maximal ideal, a map `R₀.placeMap` on places preserving degrees, compatibility of the structure maps with $A$ and with the residue map of $A$, the possibility of scaling any nonzero element into `R₀.integers` with nonzero residue, and compatibility of `placeMap` with orders of functions. The hypothesis `hR₀` requires that for every Laurent series $y$ with coefficients in $A$ whose coefficientwise image in $\overline{\mathbb{Q}}$ lies in `modularFunctionFieldBar M'`, that element lies in `R₀.integers` and its $R_0$-residue, read as a Laurent series over $k_A$, is the coefficientwise reduction of $y$ modulo the maximal ideal of $A$.
--
--   Next, $\zeta$ is an element of `Idx q` (the primitive $q$-th roots of unity in $\overline{\mathbb{Q}}$), and two families of valuation subrings of `fieldBar q M'` are given: `OIg` indexed by [`CuspidalType.ProjLine q`](def/CuspidalType_IsCuspidalOfType.html#L21) $= \mathbb{P}^1(\mathbb{Z}/q)$, and `OSS` indexed by $W$. The Igusa family is constrained by four hypotheses: `hIg_inf` describes `OIg (lineInfty q)` (the index being the point $[1:0]$) as the set of $f$ such that $f = x/y$ for Laurent series $x, y$ with coefficients in $A$ whose denominator has nonzero coefficientwise reduction; `hIg` provides, for each $\ell$, some $\gamma \in \Gamma_0(M')$ whose reduction `redQ q γ` carries $[1:0]$ to $\ell$ and with `OIg ℓ` the pullback of `OIg (lineInfty q)` along the automorphism `levelAutBar q M' ζ γ`; `hIg_inj` asserts injectivity of `OIg`; and `hIg_perm` asserts that for every $\zeta'$ in `Idx q` and $\gamma \in \Gamma_0(M')$, pullback along `levelAutBar q M' ζ' γ` permutes the family `OIg`. The supersingular family is constrained by three hypotheses: `hSS_A` says each `OSS s` cuts out $A$ on $\overline{\mathbb{Q}}$; `hSS_over` says that for $s \in W$ and $f \in$ `R₀.integers` such that $f$ has non-negative order at every place of `modularFunctionFieldBar M'` over $\overline{\mathbb{Q}}$ at which the base-changed $q$-expansion `coeffEmb (AlgebraicClosure ℚ) jq` of $j$ has non-negative order, and such that `R₀.residue f` lies in the valuation subring of the place $s$, the image of $f$ in `fieldBar q M'` lies in `OSS s`, and moreover for every $a \in A$ whose residue equals $s$`.evalAt (R₀.residue f)` the difference of that image and the image of $a$ lies in the maximal ideal of `OSS s`; `hSS_fix` says each `OSS s` is invariant under pullback along every `levelAutBar q M' ζ' γ` with $\gamma \in \Gamma_0(M')$; and `hSS_tr` provides for each $s$ an element $t \in$ `OSS s` such that $t - a$ is a unit of `OSS s` for every $a \in A$.
--
--   In addition, $R$ is a `RegularProlongation A` of `fieldBar q M'` with values in `xHFunctionFieldC k_A (q ^ 2 * M') (levelH q M')` (the same data as a constant reduction, without the place-theoretic clauses), subject to `hR`: `R.integers = OIg (lineInfty q)`; and `hR₀O` identifies `R₀.integers` with the preimage of `OIg (lineInfty q)` under the inclusion of `modularFunctionFieldBar M'` in `fieldBar q M'`.
--
--   The arithmetic of the base is described by the following data. There is $\pi \in A$ with $\pi^{q^2-1} = q$. There is an intermediate field $k_0$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ and an element $\pi_0 \in k_0$ lying in $A$ such that the valuation subring $A \cap k_0$ (the pullback of $A$ along $k_0 \to \overline{\mathbb{Q}}$) is a discrete valuation ring with maximal ideal generated by $\pi_0$, is Henselian, and has algebraically closed residue field; the hypothesis `hκ` requires every $a \in A$ to be congruent, modulo the maximal ideal of $A$, to some element of $k_0$ lying in $A$. There is an auxiliary prime $\ell$ with $\ell \ge 3$, $\ell \ne q$ and $\ell \nmid M'$, an element $\zeta_0 \in k_0$ which is a primitive $q\ell$-th root of unity in $\overline{\mathbb{Q}}$, and an element $\varpi_t \in k_0$ lying in $A$ with $\varpi_t^{q^2-1} = q u$ for some unit $u$ of $A$. Finally $K_1$ is an intermediate field of $\overline{\mathbb{Q}}/k_0$, finite over $k_0$, and $A_1$ is a valuation subring of $K_1$ which is exactly the set of elements of $K_1$ lying in $A$, and which is a Henselian discrete valuation ring.
--
--   Under these hypotheses the assertion is the following, `fieldBar q M'` being regarded as a $k_0$-algebra through $\overline{\mathbb{Q}}$. Let $F_0$ be an intermediate field of `fieldBar q M'` over $k_0$ such that: the compositum of $F_0$ with the $k_0$-subfield generated by the image of $\overline{\mathbb{Q}}$ is all of `fieldBar q M'`; $F_0$ is stable under `levelAutBar q M' ζ' γ` for every $\zeta'$ in `Idx q` and every $\gamma \in \Gamma_0(M')$; for every intermediate field $K'$ of $\overline{\mathbb{Q}}/k_0$ finite over $k_0$, every $m$, every $K'$-linearly independent family $c : \mathrm{Fin}\,m \to \overline{\mathbb{Q}}$ and every family $a : \mathrm{Fin}\,m \to$ `fieldBar q M'` with all $a_i$ in the compositum of $F_0$ with the $k_0$-subfield generated by the image of $K'$, the relation $\sum_i c_i a_i = 0$ forces all $a_i = 0$; and every element of `fieldBar q M'` whose underlying Laurent series lies in the range of `coeffEmb (AlgebraicClosure ℚ)` belongs to $F_0$.
--
--   Write $T_1$ for the compositum, inside `fieldBar q M'`, of $F_0$ with the $k_0$-subfield generated by the image of $K_1$. Let $T_1$ be equipped with an $A_1$-algebra structure whose structure map agrees on $A_1$ with the inclusion $K_1 \subseteq \overline{\mathbb{Q}} \to$ `fieldBar q M'`, and let $j_1 \in T_1$ have image in `fieldBar q M'` equal to the inclusion of the element `coeffEmb (AlgebraicClosure ℚ) jq` of `modularFunctionFieldBar M'`, with $j_1 \ne 0$. Let $\varpi$ generate the maximal ideal of $A_1$, and let $V$ be a valuation subring of $T_1$ such that the image of every element of $A_1$ lies in $V$, the image of $\varpi$ is a non-unit of $V$, and for every polynomial $P \in A_1[X]$ not divisible by the constant polynomial $\varpi$ both $P(j_1)$ and $P(j_1)^{-1}$ lie in $V$.
--
--   The conclusion is that there exists a point $\ell$ of $\mathbb{P}^1(\mathbb{Z}/q)$ — the bound variable of the conclusion carries the same name as the auxiliary prime above — such that for every $f \in T_1$: $f \in V$ if and only if the image of $f$ in `fieldBar q M'` lies in `OIg ℓ`. Thus $V$ is precisely the restriction to $T_1$ of one of the Igusa valuation subrings of the family `OIg`.
--
--   This is the branch-identification step on the Igusa leg of the semistable covering of the full-level modular curve: a valuation of the level field $T_1 = K_1 \cdot F_0$ that dominates $A_1$, is centred at the uniformiser $\varpi$, and sees $j_1$ as a generic (invertible modulo $\varpi$) parameter must be the trace of one of the $q+1$ Igusa valuation rings `OIg ℓ`; here $q = 2$, so $\mathbb{P}^1(\mathbb{Z}/q)$ has three points. It is used downstream to identify the components of the special fibre of the two-chart integral model and the maximal ideals of the associated chart algebras.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_forall_coe_mem_igusa_iff_of_valuationSubring_levelField_of_eq_two.lean

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

theorem ModularCurve.FullLevel.exists_forall_coe_mem_igusa_iff_of_valuationSubring_levelField_of_eq_two
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

    ∀ (ϖ : ↥A₁), IsLocalRing.maximalIdeal ↥A₁ = Ideal.span {ϖ} →
    ∀ (V : ValuationSubring ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)),
      (∀ a : ↥A₁, algebraMap ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) a ∈ V) →
      algebraMap ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) ϖ ∈ V.nonunits →
      (∀ P : Polynomial ↥A₁, ¬ (Polynomial.C ϖ ∣ P) →
        Polynomial.aeval j₁ P ∈ V ∧ (Polynomial.aeval j₁ P)⁻¹ ∈ V) →
      ∃ ℓ : CuspidalType.ProjLine q, ∀ f : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀), f ∈ V ↔ ((f : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ OIg ℓ := by sorry
