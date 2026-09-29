-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_reads_resAut_smul_and_centred_iff_of_mem_closure_levelAutBar_twoChartIntegralModel_of_eq_two
-- name    : ModularCurve.FullLevel.exists_reads_resAut_smul_and_centred_iff_of_mem_closure_levelAutBar_twoChartIntegralModel_of_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/73abb48d-db58-5fa9-95f2-0b33ad51fbb7
-- title:
--   Level automorphisms act equivariantly on good points, q=2
-- statement:
--   Throughout, $q$ is a prime with $q = 2$, $M'$ is a nonzero natural number not divisible by $q$, and $A$ is a valuation subring of $\overline{\mathbb Q}$ lying over $q$ in the sense of `LiesOverPrime`, i.e. $q$ belongs to the nonunits of $A$. Further data: a finite set $W$ of places of $\mathrm{modularFunctionFieldC}(\kappa_A, M')$ over the residue field $\kappa_A = \mathrm{ResidueField}\,A$, with `hW` asserting that $W$ is exactly the set $\mathrm{ssPlaces}\,q\,M'\,\kappa_A$ of supersingular places (those places which are rational, are affine geometric places, and whose value at $\mathrm{jGeomGen}$ lies in $\mathrm{ssJSet}\,q\,\kappa_A$); the inclusion `hle` of $\mathrm{modularFunctionFieldBar}\,M'$ into $\mathrm{fieldBar}\,q\,M' = \mathrm{xHFunctionFieldBar}(q^2M', \mathrm{levelH}\,q\,M')$ as intermediate fields of $\mathrm{LaurentSeries}\,\overline{\mathbb Q}$ over $\overline{\mathbb Q}$; a `ConstantReduction` $R_0$ of $A$ from $\mathrm{modularFunctionFieldBar}\,M'$ to $\mathrm{modularFunctionFieldC}(\kappa_A, M')$, i.e. a valuation subring $R_0.\mathrm{integers}$ contracting to $A$ along $\overline{\mathbb Q}$, a surjective residue map onto the geometric function field with kernel the maximal ideal, compatible with reduction on constants, together with the scaling clause and the degree and divisor-pushforward clauses of that structure; the hypothesis `hR₀` that this reduction is computed coefficientwise on Laurent series, namely that for every Laurent series $y$ over $A$ whose coefficientwise image in $\mathrm{LaurentSeries}\,\overline{\mathbb Q}$ lies in $\mathrm{modularFunctionFieldBar}\,M'$, that element lies in $R_0.\mathrm{integers}$ and its $R_0$-residue, read as a Laurent series over $\kappa_A$, is the coefficientwise reduction of $y$; and an element $\zeta$ of $\mathrm{Idx}\,q$, i.e. a primitive $q$-th root of unity in $\overline{\mathbb Q}$.
--
--   Two families of valuation subrings of $\mathrm{fieldBar}\,q\,M'$ are given: $O_{\mathrm{Ig}}$ indexed by the projective line $\mathrm{CuspidalType.ProjLine}\,q$ over $\mathbb F_q$, and $O_{\mathrm{SS}}$ indexed by $W$.
--
--   The Igusa group of hypotheses. `hIg_inf` identifies $O_{\mathrm{Ig}}(\mathrm{lineInfty}\,q)$ as a Gauss ring: an element $f$ lies in it precisely when there are Laurent series $x, y$ over $A$ such that the coefficientwise reduction of $y$ modulo the maximal ideal of $A$ is nonzero and $f$ times the image of $y$ equals the image of $x$. `hIg` says that for each point of the projective line there is $\gamma \in \Gamma_0(M')$ whose reduction $\mathrm{redQ}\,q\,\gamma$ carries $\mathrm{lineInfty}\,q$ to that point and for which the corresponding valuation subring is the pullback of $O_{\mathrm{Ig}}(\mathrm{lineInfty}\,q)$ along $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$. `hIg_inj` asserts injectivity of $O_{\mathrm{Ig}}$, and `hIg_perm` that for every root of unity $\zeta'$ and every $\gamma \in \Gamma_0(M')$ pullback along $\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma$ permutes the family $O_{\mathrm{Ig}}$, by some permutation of the projective line.
--
--   The supersingular group of hypotheses. `hSS_A` says each $O_{\mathrm{SS}}(s)$ contracts to $A$ along $\overline{\mathbb Q} \to \mathrm{fieldBar}\,q\,M'$. `hSS_over` relates $O_{\mathrm{SS}}(s)$ to $R_0$: for $s \in W$ and $f \in R_0.\mathrm{integers}$ such that $f$ has non-negative order at every place of $\mathrm{modularFunctionFieldBar}\,M'$ over $\overline{\mathbb Q}$ at which the element $\mathrm{coeffEmb}\,\overline{\mathbb Q}\,jq$ (the base change to $\overline{\mathbb Q}$ of the $q$-expansion of the modular invariant $j$) has non-negative order, if the $R_0$-residue of $f$ lies in the valuation subring of $s$, then the image of $f$ in $\mathrm{fieldBar}\,q\,M'$ lies in $O_{\mathrm{SS}}(s)$, and moreover for every $a \in A$ whose residue equals the value of the $R_0$-residue of $f$ at $s$, the difference between the image of $f$ and the image of $a$ lies in $O_{\mathrm{SS}}(s)$ and in its maximal ideal. `hSS_fix` asserts that every $\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma$ with $\gamma \in \Gamma_0(M')$ fixes each $O_{\mathrm{SS}}(s)$ under pullback. `hSS_tr` asserts that each $O_{\mathrm{SS}}(s)$ contains an element $t$ such that $t$ minus the image of any $a \in A$ is a unit of $O_{\mathrm{SS}}(s)$.
--
--   The prolongation group. $R$ is a `RegularProlongation` of $A$ from $\mathrm{fieldBar}\,q\,M'$ to $\mathrm{xHFunctionFieldC}(\kappa_A, q^2M', \mathrm{levelH}\,q\,M')$ — a valuation subring contracting to $A$ with surjective residue map whose kernel is the maximal ideal, compatible with reduction on constants and satisfying the scaling clause — with `hR` identifying $R.\mathrm{integers}$ with $O_{\mathrm{Ig}}(\mathrm{lineInfty}\,q)$, and `hR₀O` saying that $f \in R_0.\mathrm{integers}$ holds exactly when the image of $f$ in $\mathrm{fieldBar}\,q\,M'$ lies in $O_{\mathrm{Ig}}(\mathrm{lineInfty}\,q)$.
--
--   The arithmetic group. An element $\pi \in A$ with $\pi^{q^2-1} = q$. A subfield $k_0$ of $\overline{\mathbb Q}$ and $\pi_0 \in k_0 \cap A$ such that the contraction of $A$ to $k_0$ is a discrete valuation ring with maximal ideal generated by $\pi_0$, is henselian, and has algebraically closed residue field, together with `hκ`: every element of $A$ is congruent modulo the maximal ideal of $A$ to an element of $k_0 \cap A$. A prime $\ell \ge 3$ with $\ell \ne q$ and $\ell \nmid M'$; an element $\zeta_0 \in k_0$ which is a primitive $q\ell$-th root of unity; an element $\varpi_t \in k_0 \cap A$ with $\varpi_t^{q^2-1} = q u$ for some unit $u$ of $A$. Finally a finite extension $K_1$ of $k_0$ inside $\overline{\mathbb Q}$ and a valuation subring $A_1$ of $K_1$ which is the contraction of $A$, assumed to be a henselian discrete valuation ring.
--
--   The conclusion is stated for $\mathrm{fieldBar}\,q\,M'$ regarded as a $k_0$-algebra through $\overline{\mathbb Q}$. Let $F_0$ be any $k_0$-intermediate field of $\mathrm{fieldBar}\,q\,M'$ satisfying four conditions: the compositum of $F_0$ with the $k_0$-subfield generated by the image of $\overline{\mathbb Q}$ is everything; $F_0$ is stable under every $\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma$ with $\gamma \in \Gamma_0(M')$; a linear-disjointness clause, namely for every finite extension $K'$ of $k_0$ in $\overline{\mathbb Q}$, every $m$, every $c : \mathrm{Fin}\,m \to \overline{\mathbb Q}$ linearly independent over $K'$ and every family $a$ of elements of the compositum of $F_0$ with the $k_0$-subfield generated by the image of $K'$, the relation $\sum_i c_i a_i = 0$ forces all $a_i = 0$; and $F_0$ contains every element of $\mathrm{fieldBar}\,q\,M'$ whose underlying Laurent series lies in the range of $\mathrm{coeffEmb}\,\overline{\mathbb Q}$, i.e. has rational coefficients. Write $T_1$ for the compositum of $F_0$ with the $k_0$-subfield of $\mathrm{fieldBar}\,q\,M'$ generated by the image of $K_1$. The conclusion is further stated for any $A_1$-algebra structure on $T_1$ whose structure map agrees on $A_1 \subseteq K_1 \subseteq \overline{\mathbb Q}$ with the inclusion of $\overline{\mathbb Q}$ into $\mathrm{fieldBar}\,q\,M'$, and for any $j_1 \in T_1$, nonzero, whose image in $\mathrm{fieldBar}\,q\,M'$ is the element $\mathrm{coeffEmb}\,\overline{\mathbb Q}\,jq$ of $\mathrm{modularFunctionFieldBar}\,M'$ included via `hle`.
--
--   On the two-chart integral model $\mathfrak X = \mathrm{TwoChartIntegralModel}\,A_1\,T_1\,j_1$, the pushout of $\mathrm{Spec}$ of the two integral closures $\mathrm{chartAlgFin}$ (integral elements over $A_1[j_1]$) and $\mathrm{chartAlgInf}$ (integral over $A_1[j_1^{-1}]$) along the middle chart, five auxiliary predicates are introduced by `let`.
--
--   `InStalk x f`, for $x \in \mathfrak X$ and $f \in T_1$: for every point $y$ of $\mathrm{XFin}$ mapping to $x$ under $\iota_{\mathrm{Fin}}$ there are $g, h \in \mathrm{chartAlgFin}$ with $h \notin y$ and $f h = g$ in $T_1$, and likewise for every point $y$ of $\mathrm{XInf}$ over $x$ with $g, h \in \mathrm{chartAlgInf}$.
--
--   `InMax x f`: the same with the additional requirement $g \in y$ in both charts.
--
--   `Centred P x`, for $P$ a place of $\mathrm{fieldBar}\,q\,M'$ over $\overline{\mathbb Q}$: $P$ is rational (the map from $\overline{\mathbb Q}$ to its residue field is surjective) and for every $f \in T_1$ with `InStalk x f` the image of $f$ lies in the valuation subring of $P$, the value $P.\mathrm{evalAt}\,f$ lies in $A$, and that value has $A$-valuation less than $1$ if and only if `InMax x f` holds.
--
--   `GoodPt x`: the image of $x$ under the structure morphism to $\mathrm{Spec}\,A_1$ is the closed point of $\mathrm{Spec}\,A_1$; the only point to which $x$ specialises is $x$ itself; for every point $y$ of $\mathrm{XFin}$ over $x$, every element of $\mathrm{chartAlgFin}$ whose image in $\mathrm{fieldBar}\,q\,M'$ is a nonunit of $R.\mathrm{integers}$ lies in $y$, and similarly for $\mathrm{XInf}$ and $\mathrm{chartAlgInf}$; and for every point $y$ of $\mathrm{XFin}$ over $x$, every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi$ from $\mathrm{chartAlgFin}$ to $\Omega$ with kernel $y$, the element $\varphi(\mathrm{jChartFin})$ does not lie in $\mathrm{ssJSet}\,q\,\Omega$.
--
--   `Reads x Q`, for $Q$ a place of $\mathrm{xHFunctionFieldC}(\kappa_A, q^2M', \mathrm{levelH}\,q\,M')$ over $\kappa_A$: for every $f \in T_1$ with `InStalk x f`, the image of $f$ lies in $R.\mathrm{integers}$, its $R$-residue lies in the valuation subring of $Q$, and that residue is a nonunit of this subring if and only if `InMax x f` holds.
--
--   The assertion is then: for every $\tau$ in the subgroup of the group of $\overline{\mathbb Q}$-automorphisms of $\mathrm{fieldBar}\,q\,M'$ generated by the set of all automorphisms of the form $\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma$ with $\gamma \in \Gamma_0(M')$, every proof $h_\tau$ that $\tau$ preserves $R.\mathrm{integers}$ (an element lies in $R.\mathrm{integers}$ if and only if its $\tau$-image does), and every $x \in \mathfrak X$ with `GoodPt x`, there exists $x' \in \mathfrak X$ such that: `GoodPt x'` holds; for every place $Q$, if `Reads x Q` then `Reads x' (R.resAut τ hτ • Q)`, where $R.\mathrm{resAut}\,\tau\,h_\tau$ is the automorphism of the residue function field over $\kappa_A$ induced by $\tau$ and $\bullet$ is the action of automorphisms on places; and for every place $P$ of $\mathrm{fieldBar}\,q\,M'$ over $\overline{\mathbb Q}$, `Centred P x'` holds if and only if `Centred (τ⁻¹ • P) x` holds.
--
--   This is the equivariance step on the Igusa leg of the semistable covering of the modular curve of level $q^2M'$ in the case $q = 2$: the group generated by the level automorphisms that preserve the Gauss ring of the $\infty$-Igusa component permutes the good closed points of the special fibre of the two-chart integral model compatibly with the induced action on places of the reduced function field and on centred places. It is used in the construction of the smooth Igusa base model, [`ModularCurve.FullLevel.exists_igusaBaseModel_smoothPointStalks_of_eq_two`](thm.html#ModularCurve.FullLevel.exists_igusaBaseModel_smoothPointStalks_of_eq_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_reads_resAut_smul_and_centred_iff_of_mem_closure_levelAutBar_twoChartIntegralModel_of_eq_two.lean

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

theorem ModularCurve.FullLevel.exists_reads_resAut_smul_and_centred_iff_of_mem_closure_levelAutBar_twoChartIntegralModel_of_eq_two
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

    ∀ τ ∈ Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
        ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ},
      ∀ (hτ : ∀ f : ↥(fieldBar q M'), τ f ∈ R.integers ↔ f ∈ R.integers),
        ∀ x : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), GoodPt x → ∃ x' : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), GoodPt x' ∧
          (∀ Q, Reads x Q → Reads x' (R.resAut τ hτ • Q)) ∧
          (∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), Centred P x' ↔ Centred (τ⁻¹ • P) x) := by sorry
