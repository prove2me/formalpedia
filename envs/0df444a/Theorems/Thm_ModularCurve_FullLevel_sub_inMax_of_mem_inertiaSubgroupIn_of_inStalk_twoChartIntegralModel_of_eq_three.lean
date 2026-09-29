-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_sub_inMax_of_mem_inertiaSubgroupIn_of_inStalk_twoChartIntegralModel_of_eq_three
-- name    : ModularCurve.FullLevel.sub_inMax_of_mem_inertiaSubgroupIn_of_inStalk_twoChartIntegralModel_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/1ef508e4-f1a5-5b13-8678-ab58fde6cb41
-- title:
--   Inertia acts trivially to first order at good points, q=3
-- statement:
--   Throughout, $\overline{\mathbb Q}$ denotes `AlgebraicClosure ℚ`, and $\bar F :=$ `fieldBar q M'` is the intermediate field `xHFunctionFieldBar (q ^ 2 * M') (levelH q M')` of the Laurent series field over $\overline{\mathbb Q}$, where `levelH q M'` is the kernel of the unit-group reduction `ZMod.unitsMap (dvd_sq_mul q M')`; `modularFunctionFieldBar M'` is the base change to $\overline{\mathbb Q}$ of the full level-$M'$ modular function field, and `modularFunctionFieldC (ResidueField A) M'` is the field generated over the residue field of $A$ by the two $q$-expansions `jqModC` and `jqNModC`.
--
--   The data are: a prime $q$ with `hq3 : q = 3`; a natural number $M'$, nonzero, with $q \nmid M'$; a valuation subring $A \subseteq \overline{\mathbb Q}$ with `hA : A.LiesOverPrime q`, i.e. $q$ is a non-unit of $A$; a finite set $W$ of places of `modularFunctionFieldC (ResidueField A) M'` over `ResidueField A` which, by `hW`, consists exactly of the supersingular places `ssPlaces q M' (ResidueField A)` (rational places which are affine geometric and whose value at the geometric $j$-generator lies in `ssJSet q (ResidueField A)`); the inclusion `hle` of `modularFunctionFieldBar M'` into $\bar F$; a constant reduction $R_0$ of $A$ on `modularFunctionFieldBar M'` with residue field data in `modularFunctionFieldC (ResidueField A) M'`, together with `hR₀`, which asserts that every Laurent series $y$ over $A$ whose image over $\overline{\mathbb Q}$ lies in `modularFunctionFieldBar M'` is in $R_0$`.integers` and that its $R_0$-residue, read as a Laurent series over `ResidueField A`, is the coefficientwise reduction of $y$; a primitive $q$-th root of unity $\zeta$ (an element of `Idx q`); and two families of valuation subrings of $\bar F$, namely $O_{\mathrm{Ig}}$ indexed by the points of the projective line [`CuspidalType.ProjLine q`](def/CuspidalType_IsCuspidalOfType.html#L21) over $\mathbb Z/q$ and $O_{\mathrm{SS}}$ indexed by $W$.
--
--   Igusa hypotheses. `hIg_inf` describes $O_{\mathrm{Ig}}$ at the point `lineInfty q` $= [1:0]$ as a Gauss ring: $f \in O_{\mathrm{Ig}}(\infty)$ if and only if there are Laurent series $x,y$ over $A$ with $y$ of nonzero coefficientwise reduction and $f \cdot y = x$ after pushing $y,x$ forward to $\overline{\mathbb Q}$. `hIg` asserts that every point $L$ of the projective line is of the form `redQ q γ • lineInfty q` for some $\gamma \in \Gamma_0(M')$ with $O_{\mathrm{Ig}}(L)$ the pullback of $O_{\mathrm{Ig}}(\infty)$ along `levelAutBar q M' ζ γ`. `hIg_inj` asserts injectivity of $O_{\mathrm{Ig}}$, and `hIg_perm` that for every primitive $q$-th root of unity $\zeta'$ and every $\gamma \in \Gamma_0(M')$ the pullbacks of the $O_{\mathrm{Ig}}(L)$ along `levelAutBar q M' ζ' γ` permute the family, i.e. coincide with $O_{\mathrm{Ig}}(\sigma L)$ for a permutation $\sigma$ of the projective line.
--
--   Supersingular hypotheses. `hSS_A` says that for each $s \in W$ a constant $x \in \overline{\mathbb Q}$ lies in $O_{\mathrm{SS}}(s)$ exactly when $x \in A$. `hSS_over` says that for $s \in W$ and $f \in R_0$`.integers` such that $f$ has non-negative order at every place of `modularFunctionFieldBar M'` over $\overline{\mathbb Q}$ at which the element `coeffEmb (AlgebraicClosure ℚ) jq` has non-negative order, and such that the $R_0$-residue of $f$ lies in the valuation subring of the place $s$, the image of $f$ in $\bar F$ lies in $O_{\mathrm{SS}}(s)$, and moreover for every $a \in A$ whose residue equals the value `s.evalAt` of the $R_0$-residue of $f$, the difference of the image of $f$ and the constant $a$ lies in $O_{\mathrm{SS}}(s)$ and in its maximal ideal. `hSS_fix` says each $O_{\mathrm{SS}}(s)$ is invariant under pullback along `levelAutBar q M' ζ' γ` for all $\zeta'$ and all $\gamma \in \Gamma_0(M')$, and `hSS_tr` provides for each $s$ an element $t \in O_{\mathrm{SS}}(s)$ such that $t - a$ is a unit of $O_{\mathrm{SS}}(s)$ for every $a \in A$.
--
--   The prolongation. $R$ is a regular prolongation of $A$ on $\bar F$ with residue field `xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')`, with `hR` identifying $R$`.integers` with $O_{\mathrm{Ig}}(\infty)$, and `hR₀O` saying that an element of `modularFunctionFieldBar M'` lies in $R_0$`.integers` exactly when its image in $\bar F$ lies in $O_{\mathrm{Ig}}(\infty)$.
--
--   Uniformisers and the small field. An element $\pi \in \overline{\mathbb Q}$ with $\pi^{q^2-1} = q$ and $\pi \in A$ is given. Further, an intermediate field $k_0$ of $\overline{\mathbb Q}/\mathbb Q$ and $\pi_0 \in k_0$ with $\pi_0 \in A$ are given such that $A \cap k_0$ is a discrete valuation ring with maximal ideal generated by $\pi_0$, is henselian, and has algebraically closed residue field, and such that (`hκ`) every $a \in A$ is congruent modulo the maximal ideal of $A$ to some $c \in k_0 \cap A$.
--
--   The auxiliary prime. A prime $\ell$ with $3 \le \ell$, $\ell \ne q$ and $\ell \nmid M'$ is given, together with $\zeta_0 \in k_0$ which is a primitive $(q\ell)$-th root of unity, and $\varpi_t \in k_0$ lying in $A$ with $\varpi_t^{\,q^2-1} = q\,u$ for some unit $u$ of $A$.
--
--   The finite layer. $K_1$ is an intermediate field of $\overline{\mathbb Q}/k_0$, finite-dimensional over $k_0$, and $A_1$ is a valuation subring of $K_1$ with $A_1 = A \cap K_1$, assumed to be a henselian discrete valuation ring.
--
--   With $k_0$ acting on $\bar F$ through $\overline{\mathbb Q}$, the assertion is the following. Write, for an intermediate field $K'$ of $\overline{\mathbb Q}/k_0$, $T_{K'} :=$ `IntermediateField.adjoin ↥k₀ (image of K' in ↥(fieldBar q M')) ⊔ F₀`, and $T_1 := T_{K_1}$. Let $F_0$ be an intermediate field of $\bar F/k_0$ such that: the compositum of $F_0$ with the $k_0$-subfield generated by all constants from $\overline{\mathbb Q}$ is all of $\bar F$; $F_0$ is stable under `levelAutBar q M' ζ' γ` for all $\zeta'$ and all $\gamma \in \Gamma_0(M')$; a linear-disjointness condition holds, namely for every finite-dimensional intermediate field $K'$ of $\overline{\mathbb Q}/k_0$, every $m$, every $c : \mathrm{Fin}\,m \to \overline{\mathbb Q}$ linearly independent over $K'$ and every family $a$ of elements of $T_{K'}$ with $\sum_i c_i a_i = 0$, all $a_i$ vanish; and $F_0$ contains every element of $\bar F$ whose underlying Laurent series lies in the image of `coeffEmb (AlgebraicClosure ℚ)`, i.e. has rational coefficients. Let an $A_1$-algebra structure on $T_1$ be given which is compatible with the inclusions of $A_1 \subseteq K_1 \subseteq \overline{\mathbb Q}$ into $\bar F$, and let $j_1 \in T_1$ be the element whose image in $\bar F$ is the modular invariant `coeffEmb (AlgebraicClosure ℚ) jq` viewed in `modularFunctionFieldBar M'` and then in $\bar F$, with $j_1 \ne 0$.
--
--   On the two-chart integral model [`AlgebraicCurve.TwoChartIntegralModel ↥A₁ T₁ j₁`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) — the pushout gluing $\operatorname{Spec}$ of the integral closure `chartAlgFin` of $A_1[j_1]$ in $T_1$ and $\operatorname{Spec}$ of the integral closure `chartAlgInf` of $A_1[j_1^{-1}]$ in $T_1$ — four predicates are introduced. For a point $x$ of the model and $f \in T_1$: `InStalk x f` holds when for every point $y$ of `XFin` mapping to $x$ under `ιFin` there are $g,h \in$ `chartAlgFin` with $h \notin y$ and $f h = g$, and likewise over `XInf` with `chartAlgInf`; `InMax x f` is the same with the additional requirement $g \in y$ in each chart. For a place $P$ of $\bar F$ over $\overline{\mathbb Q}$, `Centred P x` holds when $P$ is rational and every $f$ with `InStalk x f` lies in the valuation subring of $P$, has $P$-value in $A$, and that value has $A$-valuation $< 1$ precisely when `InMax x f`. A point $x$ is a `GoodPt` when it lies over the closed point of $\operatorname{Spec} A_1$ under `toBase`, is closed (every $y$ with $x \rightsquigarrow y$ equals $x$), every chart element of either chart whose image in $\bar F$ is a non-unit of $R$`.integers` lies in the prime of every point of that chart above $x$, and for every point $y$ of `XFin` above $x$, every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi$ from `chartAlgFin` to $\Omega$ with kernel $y$, the value $\varphi(j_1)$ is not in [`ModularCurve.ssJSet q Ω`](def/ModularCurve_SupersingularModuli.html#L7). Finally, `Reads x Q`, for a place $Q$ of `xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')` over `ResidueField A`, holds when every $f$ with `InStalk x f` lies in $R$`.integers`, its $R$-residue lies in the valuation subring of $Q$, and that residue is a non-unit there exactly when `InMax x f`. The conclusion below uses only `InStalk`, `InMax` and `GoodPt`.
--
--   The conclusion: for every $\tau$ in `A.inertiaSubgroupIn ℚ` — the image in $\operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q)$ of the inertia subgroup of $A$ inside its decomposition group — such that $\tau(K_1) \subseteq K_1$, both of the following hold. First, the coefficientwise action [`ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ`](def/ModularCurve_ArithmeticGalois.html#L54) on $\bar F$ maps $T_1$ into $T_1$. Second, for every point $x$ of the two-chart integral model with `GoodPt x`, every $f \in T_1$ and every proof that $\tau \cdot f$ again lies in $T_1$: if `InStalk x f`, then `InMax x` holds for the difference of $\tau \cdot f$ and $f$, formed in $T_1$.
--
--   This is the $q = 3$ case of the statement that an inertia element at the chosen place $A$, preserving the finite layer $K_1$, acts on the local ring at any good point of the two-chart integral model of the $\infty$-Igusa branch by a first-order-trivial map: the displacement $\tau f - f$ of any stalk element lies in the maximal ideal. It is used in the construction of the smooth Igusa base model for $q = 3$ ([`ModularCurve.FullLevel.exists_igusaBaseModel_smoothPointStalks_of_eq_three`](thm.html#ModularCurve.FullLevel.exists_igusaBaseModel_smoothPointStalks_of_eq_three)), where it supplies the inertia-invariance of the smooth points and of their residue data on the Igusa leg of the semistable covering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_sub_inMax_of_mem_inertiaSubgroupIn_of_inStalk_twoChartIntegralModel_of_eq_three.lean

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

theorem ModularCurve.FullLevel.sub_inMax_of_mem_inertiaSubgroupIn_of_inStalk_twoChartIntegralModel_of_eq_three
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

    let InStalk : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) → Prop := fun x f =>
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∃ g h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), h ∉ y.asIdeal ∧ f * (h : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) = (g : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀))) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∃ g h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), h ∉ y.asIdeal ∧ f * (h : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) = (g : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)))
    let InMax : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) → Prop := fun x f =>
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∃ g h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), h ∉ y.asIdeal ∧ g ∈ y.asIdeal ∧ f * (h : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) = (g : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀))) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∃ g h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), h ∉ y.asIdeal ∧ g ∈ y.asIdeal ∧ f * (h : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) = (g : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)))
    let Centred : Place (AlgebraicClosure ℚ) ↥(fieldBar q M') → ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → Prop := fun P x =>
      P.IsRational ∧ ∀ f : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀), InStalk x f →
        (f : ↥(fieldBar q M')) ∈ P.toValuationSubring ∧ P.evalAt (f : ↥(fieldBar q M')) ∈ A ∧
          (A.valuation (P.evalAt (f : ↥(fieldBar q M'))) < 1 ↔ InMax x f)

    let GoodPt : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → Prop := fun x =>
      (AlgebraicCurve.TwoChartIntegralModel.toBase ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base x = closedPoint ↥A₁ ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), x ⤳ y → y = x) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), ((b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ R.integers.nonunits → b ∈ y.asIdeal) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), ((b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ R.integers.nonunits → b ∈ y.asIdeal) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
          (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) →+* Ω), RingHom.ker φ = y.asIdeal →
            φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) ∉ ModularCurve.ssJSet q Ω)

    let Reads : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) → Prop := fun x Q =>
      ∀ f : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀), InStalk x f →
        ∃ hR : (f : ↥(fieldBar q M')) ∈ R.integers, R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ Q.toValuationSubring ∧
          (R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ Q.toValuationSubring.nonunits ↔ InMax x f)

    ∀ τ ∈ A.inertiaSubgroupIn ℚ, (∀ a : AlgebraicClosure ℚ, a ∈ K₁ → τ a ∈ K₁) →
      (∀ f : ↥(fieldBar q M'), f ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀ →
        ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • f ∈
          IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) ∧
      ∀ x : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), GoodPt x →
        ∀ (f : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) (hτf : ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • (f : ↥(fieldBar q M')) ∈
            IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀),
          InStalk x f → InMax x (⟨_, hτf⟩ - f) := by sorry
