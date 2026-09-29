-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_sub_inMax_of_mem_inertiaSubgroupIn_of_inStalk_twoChartIntegralModel
-- name    : ModularCurve.FullLevel.sub_inMax_of_mem_inertiaSubgroupIn_of_inStalk_twoChartIntegralModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/d4a7a18f-1e59-5856-842e-d2e5d5d6937d
-- title:
--   Inertia fixes good points of the two-chart model to first order
-- statement:
--   Throughout, $q$ is a prime with $q\ge 5$ and $M'$ is a nonzero natural number with $q\nmid M'$, and $A$ is a valuation subring of $\overline{\mathbb Q}$ satisfying `A.LiesOverPrime q`, i.e. $q$ lies in the nonunits of $A$. Write $\kappa(A)$ for the residue field of $A$, write $F_{M'}:=$ `modularFunctionFieldBar M'` for the intermediate field of $\operatorname{LaurentSeries}(\overline{\mathbb Q})$ obtained from the full level-$M'$ modular function field over $\mathbb Q$ by adjoining, over $\overline{\mathbb Q}$, the coefficientwise images of its elements, and write $F:=$ `fieldBar q M'` for the corresponding base change of `xHFunctionField (q^2*M') (levelH q M')`, where `levelH q M'` is the kernel of the reduction $(\mathbb Z/q^2M')^\times\to(\mathbb Z/q)^\times$, i.e. the subgroup of units congruent to $1$ modulo $q$. The hypothesis `hle` asserts $F_{M'}\le F$. A finite set $W$ of places of `modularFunctionFieldC (ResidueField A) M'` over $\kappa(A)$ is given, and `hW` says that $W$ consists exactly of the supersingular places, that is, of the places $w$ that are rational, satisfy `IsAffineGeomPlace`, and for which $w.\mathrm{evalAt}$ of the generator `jGeomGen` lies in `ssJSet q (ResidueField A)` (the set of $j$ such that every elliptic Weierstrass curve with that $j$-invariant has no nonzero $q$-torsion point).
--
--   The reduction data consist of a `ConstantReduction` $R_0$ of $A$ from $F_{M'}$ to `modularFunctionFieldC (ResidueField A) M'` — a valuation subring $R_0.\mathrm{integers}$ of $F_{M'}$, a surjective residue homomorphism onto the reduced function field with kernel the maximal ideal, a map on places, and the compatibilities recorded in that structure (membership criterion for constants, compatibility of residues with $A\to\kappa(A)$, existence of scalings with nonzero residue, preservation of degrees and of divisors) — together with `hR₀`, which requires that every Laurent series $y$ over $A$ whose coefficientwise image in $\overline{\mathbb Q}$ lies in $F_{M'}$ is an $R_0$-integer whose residue, read as a Laurent series over $\kappa(A)$, is the coefficientwise reduction of $y$, and `hR₀O`, which identifies $R_0.\mathrm{integers}$ with the preimage in $F_{M'}$ of the valuation subring $\mathcal O_\infty:=$ `OIg (lineInfty q)` of $F$.
--
--   A primitive $q$-th root of unity $\zeta$ (an element of `Idx q`) is fixed, and two families of valuation subrings of $F$: $\mathcal O_{\mathrm{Ig}}$ indexed by $\mathbb P^1(\mathbb Z/q)$ and $\mathcal O_{\mathrm{SS}}$ indexed by $W$. The Igusa hypotheses are: `hIg_inf`, saying that $f\in\mathcal O_\infty$ at the point $[1:0]$ holds exactly when there are Laurent series $x,y$ over $A$ with $y$ having nonzero coefficientwise reduction and $f\cdot y=x$ in $\operatorname{LaurentSeries}(\overline{\mathbb Q})$ (the Gauss-ring description); `hIg`, saying that each point of $\mathbb P^1(\mathbb Z/q)$ is the image of $[1:0]$ under the reduction `redQ q γ` of some $\gamma\in\Gamma_0(M')$ for which the corresponding member of the family is the comap of $\mathcal O_\infty$ along the algebra automorphism `levelAutBar q M' ζ γ`; `hIg_inj`, injectivity of the family; and `hIg_perm`, saying that for every primitive root $\zeta'$ and every $\gamma\in\Gamma_0(M')$ the comap along `levelAutBar q M' ζ' γ` permutes the family. A `RegularProlongation` $R$ of $A$ from $F$ to `xHFunctionFieldC (ResidueField A) (q^2*M') (levelH q M')` is given with $R.\mathrm{integers}=\mathcal O_\infty$ (`hR`).
--
--   The supersingular hypotheses are: `hSS_A`, that for each $s\in W$ an element of $\overline{\mathbb Q}$ lies in $\mathcal O_{\mathrm{SS}}(s)$ exactly when it lies in $A$; `hSS_over`, that for $s\in W$ and $f$ an $R_0$-integer of $F_{M'}$ such that $P.\mathrm{ord}(f)\ge 0$ for every place $P$ of $F_{M'}$ over $\overline{\mathbb Q}$ with $P.\mathrm{ord}(j)\ge 0$ (here $j$ is the coefficientwise image in $F_{M'}$ of the $q$-expansion `jq`), and such that the $R_0$-residue of $f$ lies in the valuation subring of $s$, the image of $f$ in $F$ lies in $\mathcal O_{\mathrm{SS}}(s)$, and moreover for every $a\in A$ whose residue equals $s.\mathrm{evalAt}$ of the $R_0$-residue of $f$, the difference of the image of $f$ and the image of $a$ lies in $\mathcal O_{\mathrm{SS}}(s)$ and in its maximal ideal; `hSS_fix`, that each $\mathcal O_{\mathrm{SS}}(s)$ is its own comap along every `levelAutBar q M' ζ' γ` with $\gamma\in\Gamma_0(M')$; and `hSS_tr`, that each $\mathcal O_{\mathrm{SS}}(s)$ contains an element $t$ such that $t-a$ lies in $\mathcal O_{\mathrm{SS}}(s)$ and is a unit there for every $a\in A$.
--
--   The arithmetic of the base is constrained as follows: an element $\pi\in A$ with $\pi^{q^2-1}=q$; an intermediate field $k_0$ of $\overline{\mathbb Q}/\mathbb Q$ and $\pi_0\in k_0\cap A$ such that $A\cap k_0$ (the comap of $A$ along $k_0\to\overline{\mathbb Q}$) is a discrete valuation ring with maximal ideal generated by $\pi_0$, is henselian, and has algebraically closed residue field, together with `hκ`, which requires every $a\in A$ to be congruent modulo the maximal ideal of $A$ to some element of $k_0\cap A$; a prime $\ell$ with $\ell\ge 3$, $\ell\ne q$, $\ell\nmid M'$; an element $\zeta_0\in k_0$ which is a primitive $q\ell$-th root of unity; an element $\varpi_t\in k_0\cap A$ with $\varpi_t^{q^2-1}=q\cdot u$ for some unit $u$ of $A$; and finally an intermediate field $K_1$ of $\overline{\mathbb Q}/k_0$ of finite degree over $k_0$ and a valuation subring $A_1$ of $K_1$ which is the contraction of $A$ (that is, $x\in A_1$ iff $x\in A$ in $\overline{\mathbb Q}$), assumed to be a henselian discrete valuation ring.
--
--   With $F$ regarded as a $k_0$-algebra through $\overline{\mathbb Q}$, the assertion is made for every intermediate field $F_0$ of $F/k_0$ subject to four conditions: the compositum of $F_0$ with the $k_0$-subfield generated by the image of $\overline{\mathbb Q}$ is all of $F$; $F_0$ is stable under every `levelAutBar q M' ζ' γ` with $\gamma\in\Gamma_0(M')$; a linear-disjointness condition, namely that for every intermediate field $K'$ of $\overline{\mathbb Q}/k_0$ finite over $k_0$, every $K'$-linearly independent family $c_0,\dots,c_{m-1}$ in $\overline{\mathbb Q}$ and every family $a_0,\dots,a_{m-1}$ of elements of the compositum of $F_0$ with the $k_0$-subfield generated by the image of $K'$, the relation $\sum_i c_i a_i=0$ forces all $a_i=0$; and that every element of $F$ whose underlying Laurent series has rational coefficients (lies in the range of `coeffEmb`) belongs to $F_0$. Write $T_1$ for the compositum, inside $F$, of $F_0$ with the $k_0$-subfield generated by the image of $K_1$. An $A_1$-algebra structure on $T_1$ is assumed whose structure map is the inclusion of $A_1\subseteq K_1$ into $F$, and $j_1\in T_1$ is assumed nonzero and to have image in $F$ equal to the inclusion of the element of $F_{M'}$ given by the coefficientwise image of the $q$-expansion `jq`.
--
--   Let $B_{\mathrm{fin}}$ and $B_\infty$ denote the $A_1$-subalgebras `chartAlgFin` and `chartAlgInf` of $T_1$, consisting of the elements of $T_1$ integral over $A_1[j_1]$, respectively over $A_1[j_1^{-1}]$, let $X_{\mathrm{fin}}=\operatorname{Spec}B_{\mathrm{fin}}$ and $X_\infty=\operatorname{Spec}B_\infty$, and let $\mathfrak X:=$ [`AlgebraicCurve.TwoChartIntegralModel A₁ T₁ j₁`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) be the pushout of the two chart maps, with its structure morphism `toBase` to $\operatorname{Spec}A_1$ and with the two canonical morphisms $\iota_{\mathrm{fin}}$, $\iota_\infty$ from the charts. The statement introduces the following abbreviations for $x$ a point of $\mathfrak X$ and $f\in T_1$:
--
--   `InStalk x f`: for every prime $y$ of $B_{\mathrm{fin}}$ whose image under $\iota_{\mathrm{fin}}$ is $x$ there are $g,h\in B_{\mathrm{fin}}$ with $h\notin y$ and $f\cdot h=g$ in $T_1$, and the same with $B_\infty$, $\iota_\infty$ in place of $B_{\mathrm{fin}}$, $\iota_{\mathrm{fin}}$.
--
--   `InMax x f`: the same, with the additional requirement $g\in y$ in both clauses.
--
--   `GoodPt x`: the image of $x$ under `toBase` is the closed point of $\operatorname{Spec}A_1$; every point to which $x$ specialises equals $x$; for every $y$ in either chart lying over $x$, every element of the corresponding chart algebra whose image in $F$ is a nonunit of $R.\mathrm{integers}$ lies in $y$; and for every $y$ in $X_{\mathrm{fin}}$ over $x$, every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi$ from $B_{\mathrm{fin}}$ to $\Omega$ with kernel $y$, the value $\varphi(j_1)$ does not lie in [`ModularCurve.ssJSet q Ω`](def/ModularCurve_SupersingularModuli.html#L7).
--
--   Two further abbreviations are introduced: `Centred P x`, for $P$ a place of $F$ over $\overline{\mathbb Q}$, asserting that $P$ is rational and that every $f$ with `InStalk x f` lies in the valuation subring of $P$, has $P.\mathrm{evalAt}(f)\in A$, and satisfies: the $A$-valuation of $P.\mathrm{evalAt}(f)$ is $<1$ if and only if `InMax x f`; and `Reads x Q`, for $Q$ a place of `xHFunctionFieldC (ResidueField A) (q^2*M') (levelH q M')` over $\kappa(A)$, asserting that every $f$ with `InStalk x f` is an $R$-integer whose $R$-residue lies in the valuation subring of $Q$ and is a nonunit there if and only if `InMax x f`. Neither `Centred` nor `Reads` occurs in the conclusion.
--
--   The conclusion is: for every $\tau$ in `A.inertiaSubgroupIn ℚ`, the image in $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ of the inertia subgroup of $A$ inside its decomposition subgroup, such that $\tau$ maps $K_1$ into itself, both of the following hold. First, $T_1$ is stable under the semilinear action of [`ModularCurve.arithmeticGalois (xHFunctionField (q^2*M') (levelH q M')) τ`](def/ModularCurve_ArithmeticGalois.html#L54), which acts on $F$ by applying $\tau$ to the coefficients of $q$-expansions: for every $f\in F$ lying in $T_1$, also $\tau\cdot f$ lies in $T_1$. Second, for every point $x$ of $\mathfrak X$ with `GoodPt x`, every $f\in T_1$, and every proof that $\tau\cdot f$ lies in $T_1$, if `InStalk x f` then `InMax x (τ·f − f)`: the difference between the coefficientwise $\tau$-translate of $f$ and $f$ lies in the maximal ideal of the local ring at every point of either chart lying above $x$.
--
--   This is the inertia-invariance clause in the construction of the smooth Igusa base model: on the $\infty$-Igusa component an inertia element of $A$ acts trivially on residue fields, so at a good point of the two-chart integral model it moves each stalk element into the maximal ideal, and the residue discs attached to such points are inertia-stable. It is used by [`ModularCurve.FullLevel.exists_igusaBaseModel_smoothPointStalks`](thm.html#ModularCurve.FullLevel.exists_igusaBaseModel_smoothPointStalks).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_sub_inMax_of_mem_inertiaSubgroupIn_of_inStalk_twoChartIntegralModel.lean

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

theorem ModularCurve.FullLevel.sub_inMax_of_mem_inertiaSubgroupIn_of_inStalk_twoChartIntegralModel
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
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
