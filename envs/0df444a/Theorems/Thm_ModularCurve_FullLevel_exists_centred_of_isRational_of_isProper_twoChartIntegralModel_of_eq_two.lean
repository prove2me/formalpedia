-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_centred_of_isRational_of_isProper_twoChartIntegralModel_of_eq_two
-- name    : ModularCurve.FullLevel.exists_centred_of_isRational_of_isProper_twoChartIntegralModel_of_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/7b770927-e5bf-52da-8b28-4977b64ed156
-- title:
--   Centring rational places on the proper two-chart model, q = 2
-- statement:
--   The setting is that of the integral (Igusa) model of the full-level modular function field at the prime $q$ with $q = 2$ (the hypothesis `hq2`), with a level $M'$ that is non-zero and prime to $q$ (`hqM'`).
--
--   **Valuation data and reduction of the level-$M'$ field.** Let $A$ be a valuation subring of $\overline{\mathbb Q}$ lying over $q$ in the sense of `LiesOverPrime`, i.e. $q$ is a non-unit of $A$ (`hA`). Let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}(\mathrm{ResidueField}\,A, M')$ over the residue field of $A$ which, by `hW`, consists exactly of the supersingular places `ssPlaces q M' (ResidueField A)`: the places $w$ that are rational, are affine geometric places, and satisfy $w.\mathrm{evalAt}(\mathrm{jGeomGen})\in \mathrm{ssJSet}\,q$. The inclusion `hle` asserts $\mathrm{modularFunctionFieldBar}\,M' \le \mathrm{fieldBar}\,q\,M'$, the first field being the $\overline{\mathbb Q}$-base change (inside Laurent series over $\overline{\mathbb Q}$) of the full level-$M'$ function field, the second the base change of the $X_H$-function field of level $q^2M'$ with $H = \mathrm{levelH}\,q\,M'$. Further, $R_0$ is a `ConstantReduction` of $A$ from $\mathrm{modularFunctionFieldBar}\,M'$ to $\mathrm{modularFunctionFieldC}(\mathrm{ResidueField}\,A,M')$, that is: a valuation subring $R_0.\mathrm{integers}$, a surjective residue homomorphism onto the target with kernel the maximal ideal, a map on places, the compatibilities $\mathrm{algebraMap}\,x \in R_0.\mathrm{integers} \iff x \in A$ and $R_0.\mathrm{residue}\circ\mathrm{algebraMap} = \mathrm{algebraMap}\circ\mathrm{residue}_A$, the scaling property `exists_smul_mem`, and preservation of degrees and of divisors under the place map. The hypothesis `hR₀` says that for every Laurent series $y$ with coefficients in $A$ whose coefficientwise image lies in $\mathrm{modularFunctionFieldBar}\,M'$, that element lies in $R_0.\mathrm{integers}$ and its $R_0$-residue, read as a Laurent series over $\mathrm{ResidueField}\,A$, is the coefficientwise reduction of $y$. Finally $\zeta$ is a primitive $q$-th root of unity in $\overline{\mathbb Q}$ (an element of `Idx q`).
--
--   **The two families of valuation subrings.** Let $O_{\mathrm{Ig}}$ be a family of valuation subrings of $\mathrm{fieldBar}\,q\,M'$ indexed by $\mathbb P^1(\mathbb Z/q)$ and $O_{\mathrm{SS}}$ one indexed by $W$. They are constrained as follows. `hIg_inf` describes the ring at the line at infinity: $f \in O_{\mathrm{Ig}}(\mathrm{lineInfty}\,q)$ if and only if $f$ is a quotient $x/y$ of Laurent series with coefficients in $A$, in the sense that $f\cdot \bar y = \bar x$ for Laurent series $x,y$ over $A$ with the reduction of $y$ non-zero. `hIg` says every index $\ell$ is reached from $\mathrm{lineInfty}\,q$ by some $\gamma \in \Gamma_0(M')$ (acting through $\mathrm{redQ}\,q$ on $\mathbb P^1(\mathbb Z/q)$) and that $O_{\mathrm{Ig}}(\ell)$ is then the pullback of $O_{\mathrm{Ig}}(\mathrm{lineInfty}\,q)$ along $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$; `hIg_inj` says $O_{\mathrm{Ig}}$ is injective; `hIg_perm` says that for each primitive root $\zeta'$ and each $\gamma \in \Gamma_0(M')$ the pullbacks along $\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma$ permute the family, i.e. agree with $O_{\mathrm{Ig}}\circ\sigma$ for some permutation $\sigma$ of $\mathbb P^1(\mathbb Z/q)$.
--
--   For the supersingular family: `hSS_A` says that for each $s \in W$ the constants in $O_{\mathrm{SS}}(s)$ are exactly the image of $A$. `hSS_over` says that for $s \in W$ and $f \in R_0.\mathrm{integers}$ such that $f$ has non-negative order at every place of $\mathrm{modularFunctionFieldBar}\,M'$ over $\overline{\mathbb Q}$ at which the coefficient embedding of the $q$-expansion $\mathrm{jq}$ has non-negative order, and such that the $R_0$-residue of $f$ lies in the valuation subring of the place $s$, one has: the image of $f$ in $\mathrm{fieldBar}\,q\,M'$ lies in $O_{\mathrm{SS}}(s)$, and for every $a \in A$ whose residue equals $s.\mathrm{evalAt}$ of the $R_0$-residue of $f$, the difference of that image and $a$ lies in the maximal ideal of $O_{\mathrm{SS}}(s)$. `hSS_fix` says each $O_{\mathrm{SS}}(s)$ is stable under pullback along $\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma$ for all $\zeta'$ and all $\gamma \in \Gamma_0(M')$. `hSS_tr` provides, for each $s \in W$, an element $t \in O_{\mathrm{SS}}(s)$ such that $t - a$ is a unit of $O_{\mathrm{SS}}(s)$ for every $a \in A$.
--
--   Let $R$ be a `RegularProlongation` of $A$ from $\mathrm{fieldBar}\,q\,M'$ to $\mathrm{xHFunctionFieldC}(\mathrm{ResidueField}\,A, q^2M', \mathrm{levelH}\,q\,M')$ — a valuation subring with a surjective residue map whose kernel is the maximal ideal, compatible with $A$ and its residue field, together with `exists_smul_mem` — whose ring of integers is $O_{\mathrm{Ig}}(\mathrm{lineInfty}\,q)$ (`hR`); and let `hR₀O` say that $f \in R_0.\mathrm{integers}$ if and only if the image of $f$ in $\mathrm{fieldBar}\,q\,M'$ lies in $O_{\mathrm{Ig}}(\mathrm{lineInfty}\,q)$.
--
--   **Arithmetic of the base.** There is $\pi \in \overline{\mathbb Q}\cap A$ with $\pi^{q^2-1} = q$. There is an intermediate field $k_0$ of $\overline{\mathbb Q}/\mathbb Q$ and $\pi_0 \in k_0\cap A$ such that $A \cap k_0$ is a discrete valuation ring (`hdvr`) with maximal ideal generated by $\pi_0$ (`hunif`), is henselian local (`hhens`) and has algebraically closed residue field (`hres`); `hκ` says every element of $A$ is congruent modulo the maximal ideal of $A$ to an element of $k_0 \cap A$. There is an auxiliary prime $\ell$ with $3 \le \ell$, $\ell \ne q$, $\ell \nmid M'$, an element $\zeta_0 \in k_0$ that is a primitive $q\ell$-th root of unity, and an element $\varpi_t \in k_0 \cap A$ with $\varpi_t^{q^2-1} = q\,u$ for some unit $u$ of $A$. Finally $K_1$ is a finite extension of $k_0$ inside $\overline{\mathbb Q}$ and $A_1$ a valuation subring of $K_1$ consisting exactly of the elements of $K_1$ lying in $A$ (`hA₁`), assumed a henselian discrete valuation ring.
--
--   **The geometric frame.** With $k_0$ acting on $\mathrm{fieldBar}\,q\,M'$ through $\overline{\mathbb Q}$, the assertion is universally quantified over intermediate fields $F_0$ of $\mathrm{fieldBar}\,q\,M'$ over $k_0$ subject to four conditions: $F_0$ together with the subfield generated by all constants from $\overline{\mathbb Q}$ generates everything; $F_0$ is stable under every $\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma$ with $\gamma \in \Gamma_0(M')$; a linear-disjointness condition — for every finite extension $K'$ of $k_0$ in $\overline{\mathbb Q}$, every $K'$-linearly independent family $c : \mathrm{Fin}\,m \to \overline{\mathbb Q}$ and every family $a$ of elements of $k_0(K') \vee F_0$ (the join, inside $\mathrm{fieldBar}\,q\,M'$, of the $k_0$-subfield generated by the image of $K'$ with $F_0$), a relation $\sum_i c_i\,a_i = 0$ forces all $a_i = 0$; and every element of $\mathrm{fieldBar}\,q\,M'$ whose Laurent series lies in the image of the coefficient embedding from Laurent series over $\mathbb Q$ belongs to $F_0$.
--
--   Write $E_1 := k_0(K_1) \vee F_0$ for the join inside $\mathrm{fieldBar}\,q\,M'$ of the $k_0$-subfield generated by the image of $K_1$ with $F_0$. The assertion is further quantified over $A_1$-algebra structures on $E_1$ whose structure map is the one induced by $\overline{\mathbb Q}$, and over elements $j_1 \in E_1$ whose image in $\mathrm{fieldBar}\,q\,M'$ is the coefficient embedding of $\mathrm{jq}$ (transported by `hle`), with $j_1 \ne 0$. For such data let $\mathfrak X_1 := \mathrm{TwoChartIntegralModel}\,A_1\,E_1\,j_1$, the pushout of the two affine charts $X_{\mathrm{Fin}} = \operatorname{Spec}$ of the integral closure of $A_1[j_1]$ in $E_1$ and $X_{\mathrm{Inf}} = \operatorname{Spec}$ of the integral closure of $A_1[j_1^{-1}]$ in $E_1$, with structure morphism $\mathrm{toBase} : \mathfrak X_1 \to \operatorname{Spec} A_1$ and chart immersions $\iota_{\mathrm{Fin}}, \iota_{\mathrm{Inf}}$. The remaining hypothesis is that $\mathrm{toBase}$ is proper.
--
--   **The auxiliary predicates.** Three predicates are introduced by `let`. For $x \in \mathfrak X_1$ and $f \in E_1$, $\mathrm{InStalk}\,x\,f$ holds when for every point $y$ of $X_{\mathrm{Fin}}$ with $\iota_{\mathrm{Fin}}(y) = x$ there are $g,h$ in the first chart algebra with $h \notin y$ and $f\,h = g$ in $E_1$, and likewise for every point $y$ of $X_{\mathrm{Inf}}$ over $x$ with the second chart algebra; $\mathrm{InMax}\,x\,f$ is the same with the extra requirement $g \in y$ in both clauses. For a place $P$ of $\mathrm{fieldBar}\,q\,M'$ over $\overline{\mathbb Q}$, $\mathrm{Centred}\,P\,x$ holds when $P$ is rational (the structure map $\overline{\mathbb Q} \to$ residue field of $P$ is surjective) and, for every $f \in E_1$ with $\mathrm{InStalk}\,x\,f$: the image of $f$ lies in the valuation subring of $P$, the value $P.\mathrm{evalAt}(f)$ lies in $A$, and $A$-$\mathrm{valuation}(P.\mathrm{evalAt}(f)) < 1$ if and only if $\mathrm{InMax}\,x\,f$. A fourth predicate $\mathrm{GoodPt}$ is also introduced by `let` — $x$ lies over the closed point of $\operatorname{Spec} A_1$, specialises only to itself, every element of either chart algebra whose image is a non-unit of $R.\mathrm{integers}$ lies in the corresponding prime $y$, and for every point $y$ of $X_{\mathrm{Fin}}$ over $x$, every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi$ from the first chart algebra to $\Omega$ with kernel $y$, the element $\varphi(\mathrm{jChartFin})$ avoids $\mathrm{ssJSet}\,q\,\Omega$ — but the conclusion does not refer to $\mathrm{GoodPt}$.
--
--   **Conclusion.** For every place $P$ of $\mathrm{fieldBar}\,q\,M'$ over $\overline{\mathbb Q}$ that is rational there exists a point $x$ of $\mathfrak X_1$ such that: $\mathrm{toBase}$ sends $x$ to the closed point of $\operatorname{Spec} A_1$; $x$ specialises only to itself, i.e. $x \rightsquigarrow y$ implies $y = x$; and $\mathrm{Centred}\,P\,x$ holds.
--
--   This is the valuative-criterion step on the Igusa leg of the semistable-covering analysis at $q = 2$: a proper two-chart integral model over a henselian discrete valuation ring receives every $\overline{\mathbb Q}$-rational place of its function field at a closed point of the special fibre, compatibly with the valuation on $A$ in both directions (integrality of values and the maximal-ideal dichotomy). It is used by the results that move such a centre by a level automorphism `levelAutBar` to a point avoiding the supersingular locus, respectively away from the supersingular tubes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_centred_of_isRational_of_isProper_twoChartIntegralModel_of_eq_two.lean

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

theorem ModularCurve.FullLevel.exists_centred_of_isRational_of_isProper_twoChartIntegralModel_of_eq_two
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

    IsProper (AlgebraicCurve.TwoChartIntegralModel.toBase ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) →

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

    ∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), P.IsRational →
      ∃ x : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁),
        (AlgebraicCurve.TwoChartIntegralModel.toBase ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base x = closedPoint ↥A₁ ∧
        (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), x ⤳ y → y = x) ∧
        Centred P x := by sorry
