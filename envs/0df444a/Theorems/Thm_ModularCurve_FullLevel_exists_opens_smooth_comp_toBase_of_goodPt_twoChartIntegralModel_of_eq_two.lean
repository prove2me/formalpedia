-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_opens_smooth_comp_toBase_of_goodPt_twoChartIntegralModel_of_eq_two
-- name    : ModularCurve.FullLevel.exists_opens_smooth_comp_toBase_of_goodPt_twoChartIntegralModel_of_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/12ead5af-724d-59bc-9207-781651abcb08
-- title:
--   Smooth neighbourhood at a good point, q=2
-- statement:
--   Fix a prime $q$ with $q=2$ and a nonzero level $M'$ with $q\nmid M'$, and a valuation subring $A$ of $\overline{\mathbb Q}=\mathrm{AlgebraicClosure}\ \mathbb Q$ satisfying `A.LiesOverPrime q`, i.e. $q$ lies in `A.nonunits`. Write $k_A=$ `ResidueField A`.
--
--   *Supersingular places.* $W$ is a finite set of places of $\mathrm{modularFunctionFieldC}\ k_A\ M'$ over $k_A$, and `hW` says that $W$ consists exactly of the members of `ssPlaces q M' k_A`, that is, of the places $w$ that are rational (the structure map $k_A\to w$'s residue field is surjective), are affine geometric places, and satisfy $w.\mathrm{evalAt}(\mathrm{jGeomGen}\ k_A\ M')\in \mathrm{ssJSet}\ q\ k_A$, the set of $j$-values all of whose elliptic Weierstrass curves have trivial $q$-torsion.
--
--   *The two function fields.* `hle` asserts the inclusion $\mathrm{modularFunctionFieldBar}\ M'\le \mathrm{fieldBar}\ q\ M'$ of intermediate fields of $\overline{\mathbb Q}\subseteq \mathrm{LaurentSeries}\ \overline{\mathbb Q}$, the second being $\mathrm{xHFunctionFieldBar}(q^2M',\ \mathrm{levelH}\ q\ M')$.
--
--   *Constant reduction.* $R_0$ is a `ConstantReduction` of $A$ on $\mathrm{modularFunctionFieldBar}\ M'$ with values in $\mathrm{modularFunctionFieldC}\ k_A\ M'$: a valuation subring `R₀.integers`, a surjective ring map `R₀.residue` on it with kernel the maximal ideal, compatible with $A$ and its residue map, together with a place map of the prescribed degree and divisor behaviour. The hypothesis `hR₀` states that for every Laurent series $y$ over $A$ whose coefficientwise image in $\mathrm{LaurentSeries}\ \overline{\mathbb Q}$ lies in $\mathrm{modularFunctionFieldBar}\ M'$, that element lies in `R₀.integers` and its $R_0$-residue, viewed in $\mathrm{LaurentSeries}\ k_A$, is the coefficientwise residue of $y$.
--
--   *Branch data.* $\zeta$ is an index in `Idx q` (a primitive $q$-th root of unity in $\overline{\mathbb Q}$), and two families of valuation subrings of $\mathrm{fieldBar}\ q\ M'$ are given: $O_{\mathrm{Ig}}$ indexed by the projective line $\mathbb P^1(\mathbb F_q)$ ([`CuspidalType.ProjLine q`](def/CuspidalType_IsCuspidalOfType.html#L21)), and $O_{\mathrm{SS}}$ indexed by $W$.
--
--   The *Igusa group* of hypotheses concerns $O_{\mathrm{Ig}}$: `hIg_inf` describes $O_{\mathrm{Ig}}(\mathrm{lineInfty}\ q)$ as a Gauss-type ring, namely $f$ belongs to it precisely when there are Laurent series $x,y$ over $A$ with the coefficientwise residue of $y$ nonzero and $f\cdot y=x$ after mapping coefficients along $A\hookrightarrow\overline{\mathbb Q}$; `hIg` says every line $\ell$ is $\mathrm{redQ}\ q\ \gamma\cdot\mathrm{lineInfty}\ q$ for some $\gamma\in\Gamma_0(M')$ with $O_{\mathrm{Ig}}(\ell)$ the pullback of $O_{\mathrm{Ig}}(\mathrm{lineInfty}\ q)$ along $\mathrm{levelAutBar}\ q\ M'\ \zeta\ \gamma$; `hIg_inj` says $O_{\mathrm{Ig}}$ is injective; `hIg_perm` says that for every index $\zeta'$ and every $\gamma\in\Gamma_0(M')$ pullback along $\mathrm{levelAutBar}\ q\ M'\ \zeta'\ \gamma$ permutes the family $O_{\mathrm{Ig}}$.
--
--   The *supersingular group* concerns $O_{\mathrm{SS}}$: `hSS_A` says that for each $s\in W$ an element of $\overline{\mathbb Q}$ maps into $O_{\mathrm{SS}}(s)$ exactly when it lies in $A$; `hSS_fix` says each $O_{\mathrm{SS}}(s)$ is invariant under pullback along $\mathrm{levelAutBar}\ q\ M'\ \zeta'\ \gamma$ for all $\zeta'$ and all $\gamma\in\Gamma_0(M')$; `hSS_tr` provides, for each $s$, an element $t\in O_{\mathrm{SS}}(s)$ such that $t-a$ is a unit of $O_{\mathrm{SS}}(s)$ for every $a\in A$; and `hSS_over` is the compatibility of $O_{\mathrm{SS}}(s)$ with $R_0$ and $s$: for $f\in$ `R₀.integers` such that $0\le P.\mathrm{ord}(f)$ at every place $P$ of $\mathrm{modularFunctionFieldBar}\ M'$ over $\overline{\mathbb Q}$ at which the element given by $\mathrm{coeffEmb}\ \overline{\mathbb Q}\ \mathrm{jq}$ has nonnegative order, if the $R_0$-residue of $f$ lies in the valuation subring of $s$, then the image of $f$ in $\mathrm{fieldBar}\ q\ M'$ lies in $O_{\mathrm{SS}}(s)$, and for every $a\in A$ whose residue equals $s.\mathrm{evalAt}$ of that $R_0$-residue the difference between the image of $f$ and the image of $a$ lies in the maximal ideal of $O_{\mathrm{SS}}(s)$.
--
--   *Prolongation.* $R$ is a `RegularProlongation` of $A$ on $\mathrm{fieldBar}\ q\ M'$ with values in $\mathrm{xHFunctionFieldC}\ k_A\ (q^2M')\ (\mathrm{levelH}\ q\ M')$ — a valuation subring with a surjective residue map whose kernel is the maximal ideal, extending $A$ and its residue map, and with the scaling property — subject to `hR`: `R.integers` $=O_{\mathrm{Ig}}(\mathrm{lineInfty}\ q)$; and `hR₀O` identifies `R₀.integers` with the preimage of $O_{\mathrm{Ig}}(\mathrm{lineInfty}\ q)$ under the inclusion of $\mathrm{modularFunctionFieldBar}\ M'$ into $\mathrm{fieldBar}\ q\ M'$.
--
--   *Uniformisers and base field.* An element $\pi\in A$ with $\pi^{q^2-1}=q$ is given. Further, $k_0$ is an intermediate field of $\mathbb Q\subseteq\overline{\mathbb Q}$ and $\pi_0\in k_0$ lies in $A$; the contraction of $A$ to $k_0$ is a discrete valuation ring with maximal ideal generated by $\pi_0$, is henselian, and has algebraically closed residue field; and `hκ` says every $a\in A$ differs from some element of $k_0\cap A$ by an element of the maximal ideal of $A$.
--
--   *Auxiliary prime and twisting data.* $\ell$ is a prime with $3\le\ell$, $\ell\ne q$, $\ell\nmid M'$; $\zeta_0\in k_0$ is a primitive $q\ell$-th root of unity; and $\varpi_t\in k_0$ lies in $A$ and satisfies $\varpi_t^{\,q^2-1}=q\cdot u$ for some unit $u$ of $A$.
--
--   *Finite layer.* $K_1$ is a finite extension of $k_0$ inside $\overline{\mathbb Q}$, and $A_1$ is a valuation subring of $K_1$ with $x\in A_1\iff x\in A$, assumed to be a henselian discrete valuation ring.
--
--   With $\overline{\mathbb Q}\subseteq\mathrm{fieldBar}\ q\ M'$ making the latter a $k_0$-algebra, the assertion is the following. Let $F_0$ be an intermediate field of $k_0\subseteq\mathrm{fieldBar}\ q\ M'$ such that: the join of $F_0$ with the $k_0$-subfield generated by the image of $\overline{\mathbb Q}$ is everything; $F_0$ is stable under $\mathrm{levelAutBar}\ q\ M'\ \zeta'\ \gamma$ for all $\zeta'$ and all $\gamma\in\Gamma_0(M')$; for every finite extension $K'$ of $k_0$ in $\overline{\mathbb Q}$, every $m$, every $c:\mathrm{Fin}\ m\to\overline{\mathbb Q}$ linearly independent over $K'$ and every $a:\mathrm{Fin}\ m\to\mathrm{fieldBar}\ q\ M'$ with all $a_i$ in the join $T'$ of $F_0$ with the $k_0$-subfield generated by the image of $K'$, the relation $\sum_i c_i a_i=0$ forces $a_i=0$ for all $i$; and every element of $\mathrm{fieldBar}\ q\ M'$ whose Laurent series lies in the range of $\mathrm{coeffEmb}\ \overline{\mathbb Q}$ belongs to $F_0$.
--
--   Put $T_1$ for the join of $F_0$ with the $k_0$-subfield of $\mathrm{fieldBar}\ q\ M'$ generated by the image of $K_1$. Assume $T_1$ carries an $A_1$-algebra structure whose structure map agrees on $A_1\subseteq K_1$ with the inclusion of $\overline{\mathbb Q}$ into $\mathrm{fieldBar}\ q\ M'$, and let $j_1\in T_1$ be nonzero with image in $\mathrm{fieldBar}\ q\ M'$ equal to the inclusion along `hle` of the element of $\mathrm{modularFunctionFieldBar}\ M'$ given by $\mathrm{coeffEmb}\ \overline{\mathbb Q}\ \mathrm{jq}$.
--
--   On the two-chart integral model $\mathfrak X_1=\mathrm{TwoChartIntegralModel}\ A_1\ T_1\ j_1$, the pushout of $\mathrm{Spec}$ of the inclusions of the two chart algebras (elements of $T_1$ integral over $A_1[j_1]$, respectively over $A_1[j_1^{-1}]$), a point $x$ is called *good* when all five of the following hold: (1) $\mathrm{toBase}$ sends $x$ to the closed point of $\mathrm{Spec}\ A_1$; (2) $x$ is closed, i.e. every $y$ to which $x$ specialises equals $x$; (3) for every point $y$ of the finite chart $\mathrm{XFin}$ with $\iota_{\mathrm{Fin}}(y)=x$, every element $b$ of the finite chart algebra whose image in $\mathrm{fieldBar}\ q\ M'$ lies in `R.integers.nonunits` belongs to the prime $y$; (4) the same condition for the chart at infinity, $\mathrm{XInf}$, $\iota_{\mathrm{Inf}}$ and the chart algebra of $j_1^{-1}$; (5) for every $y$ in $\mathrm{XFin}$ over $x$, every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi$ from the finite chart algebra to $\Omega$ with kernel the prime $y$, the value $\varphi(\mathrm{jChartFin})$ does not lie in $\mathrm{ssJSet}\ q\ \Omega$.
--
--   The conclusion: for every good point $x$ of $\mathfrak X_1$ there exists an open subscheme $U$ of $\mathfrak X_1$ with $x\in U$ such that the open immersion $U.\iota$ followed by $\mathrm{toBase}:\mathfrak X_1\to\mathrm{Spec}\ A_1$ is a smooth morphism.
--
--   This is the per-point smoothness step on the $\infty$-Igusa branch of the two-chart integral model of the full-level modular curve in the case $q=2$: a closed point of the special fibre that lies on the branch cut out by the non-units of the Gauss ring `R.integers` and whose $j$-value is not supersingular has a neighbourhood smooth over $\mathrm{Spec}\,A_1$. It is used in the descent form of the same statement and in the construction of étale coordinates at points off the branch locus.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_opens_smooth_comp_toBase_of_goodPt_twoChartIntegralModel_of_eq_two.lean

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

open CategoryTheory AlgebraicGeometry AlgebraicCurve ModularCurve IsLocalRing CongruenceSubgroup
open ModularCurve.FullLevel
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem ModularCurve.FullLevel.exists_opens_smooth_comp_toBase_of_goodPt_twoChartIntegralModel_of_eq_two
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

    ∀ (x : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁)), GoodPt x →
      ∃ U : (AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).Opens,
        x ∈ U ∧ Smooth (U.ι ≫ AlgebraicCurve.TwoChartIntegralModel.toBase ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) := by sorry
