-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_constantTerm_chartAlgInf_twoChartIntegralModel_levelField
-- name    : ModularCurve.FullLevel.exists_constantTerm_chartAlgInf_twoChartIntegralModel_levelField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/7144402e-e700-5a79-8f07-4173767602ab
-- title:
--   Constant-term retraction on the pole chart at ∞
-- statement:
--   Throughout, $\overline{\mathbb Q}$ denotes `AlgebraicClosure ℚ`, and function fields are realised as intermediate fields of the Laurent series field over the relevant coefficient field, $q$-expansions being the coordinate.
--
--   **Base data.** A prime $q$ with $5 \le q$, a natural number $M' \neq 0$ with $q \nmid M'$, and a valuation subring $A \subseteq \overline{\mathbb Q}$ with `hA : A.LiesOverPrime q`, i.e. $q$ is a non-unit of $A$. Further: a finite set $W$ of places of $\mathrm{modularFunctionFieldC}(\mathrm{ResidueField}\,A, M')$ over the residue field of $A$, with `hW` asserting that $W$ consists exactly of the members of `ssPlaces q M' (ResidueField A)`, that is, the places $w$ that are rational, are affine geometric places, and satisfy $w.\mathrm{evalAt}(\mathrm{jGeomGen}) \in \mathrm{ssJSet}\,q$; and `hle`, the inclusion $\mathrm{modularFunctionFieldBar}\,M' \le \mathrm{fieldBar}\,q\,M'$ of intermediate fields of $\mathrm{LaurentSeries}(\overline{\mathbb Q})$ over $\overline{\mathbb Q}$, where $\mathrm{fieldBar}\,q\,M' = \mathrm{xHFunctionFieldBar}(q^2M', \mathrm{levelH}\,q\,M')$.
--
--   **Constant reduction.** A datum $R_0$ of type `ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M')`: a valuation subring $R_0.\mathrm{integers}$ of $\mathrm{modularFunctionFieldBar}\,M'$, a surjective ring map $R_0.\mathrm{residue}$ from it onto the characteristic-$q$ modular function field with kernel the maximal ideal, a map $R_0.\mathrm{placeMap}$ on places preserving degrees and compatible with divisor push-forward, the condition that a constant from $\overline{\mathbb Q}$ lies in $R_0.\mathrm{integers}$ precisely when it lies in $A$ (its residue then being the reduction of the constant), and the property that every non-zero element becomes an element of $R_0.\mathrm{integers}$ with non-zero residue after scaling by a suitable constant. The hypothesis `hR₀` states that for every Laurent series $y$ with coefficients in $A$ whose coefficientwise image in $\overline{\mathbb Q}$ lies in $\mathrm{modularFunctionFieldBar}\,M'$, that element lies in $R_0.\mathrm{integers}$ and its $R_0$-residue, read as a Laurent series over the residue field of $A$, is the coefficientwise reduction of $y$.
--
--   **Igusa rings.** An index $\zeta \in \mathrm{Idx}\,q$, i.e. a primitive $q$-th root of unity in $\overline{\mathbb Q}$, a family $O_{\mathrm{Ig}}$ of valuation subrings of $\mathrm{fieldBar}\,q\,M'$ indexed by the projective line over $\mathbb Z/q$, and a family $O_{\mathrm{SS}}$ of valuation subrings indexed by $W$. Four hypotheses on $O_{\mathrm{Ig}}$: `hIg_inf` identifies $O_{\mathrm{Ig}}(\mathrm{lineInfty}\,q)$ as the Gauss-type ring, namely $f$ belongs to it if and only if there are Laurent series $x, y$ with coefficients in $A$ such that the coefficientwise reduction of $y$ is non-zero and $f \cdot y = x$ after coefficientwise inclusion of $A$ into $\overline{\mathbb Q}$; `hIg` asserts that every index $\ell$ is reached from $\mathrm{lineInfty}\,q$ by the mod-$q$ reduction of some $\gamma \in \Gamma_0(M')$, with $O_{\mathrm{Ig}}(\ell)$ the preimage of $O_{\mathrm{Ig}}(\mathrm{lineInfty}\,q)$ under $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$; `hIg_inj` asserts injectivity of $O_{\mathrm{Ig}}$; `hIg_perm` asserts that for each $\zeta'$ and each $\gamma \in \Gamma_0(M')$ the operation of taking preimages under $\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma$ permutes the family $O_{\mathrm{Ig}}$.
--
--   **Supersingular rings.** Four hypotheses on $O_{\mathrm{SS}}$: `hSS_A` says that a constant from $\overline{\mathbb Q}$ lies in $O_{\mathrm{SS}}(s)$ exactly when it lies in $A$; `hSS_over` says that for $s \in W$ and $f \in R_0.\mathrm{integers}$ such that $f$ has non-negative order at every place of $\mathrm{modularFunctionFieldBar}\,M'$ over $\overline{\mathbb Q}$ at which the element $\mathrm{coeffEmb}_{\overline{\mathbb Q}}(\mathrm{jq})$ has non-negative order, and whose $R_0$-residue lies in the valuation subring of the place $s$, the image of $f$ in $\mathrm{fieldBar}\,q\,M'$ lies in $O_{\mathrm{SS}}(s)$, and moreover for every $a \in A$ whose reduction equals $s.\mathrm{evalAt}$ of the $R_0$-residue of $f$, the difference of the image of $f$ and the constant $a$ lies in $O_{\mathrm{SS}}(s)$ and in fact in its maximal ideal; `hSS_fix` says each $O_{\mathrm{SS}}(s)$ is its own preimage under $\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma$ for every $\zeta'$ and every $\gamma \in \Gamma_0(M')$; `hSS_tr` provides, for each $s \in W$, an element $t \in O_{\mathrm{SS}}(s)$ such that $t - a$ is a unit of $O_{\mathrm{SS}}(s)$ for every constant $a \in A$.
--
--   **Prolongation at $\infty$.** A datum $R$ of type `RegularProlongation A ↥(fieldBar q M') (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))` — a valuation subring $R.\mathrm{integers}$, a surjective residue map onto the characteristic-$q$ level field with kernel the maximal ideal, the constants condition relating $R.\mathrm{integers}$ to $A$, and the scaling property — together with `hR : R.integers = OIg (lineInfty q)` and `hR₀O`, which says that $f \in R_0.\mathrm{integers}$ if and only if its image in $\mathrm{fieldBar}\,q\,M'$ lies in $O_{\mathrm{Ig}}(\mathrm{lineInfty}\,q)$.
--
--   **Uniformiser and small constants.** An element $\pi \in \overline{\mathbb Q}$ with $\pi^{q^2-1} = q$ and $\pi \in A$. An intermediate field $k_0$ of $\overline{\mathbb Q}/\mathbb Q$ and $\pi_0 \in k_0$ with $\pi_0 \in A$, such that $A \cap k_0$ is a discrete valuation ring (`hdvr`) whose maximal ideal is generated by $\pi_0$ (`hunif`), is henselian (`hhens`) and has algebraically closed residue field (`hres`), and such that every $a \in A$ is congruent modulo the maximal ideal of $A$ to some element of $k_0$ lying in $A$ (`hκ`).
--
--   **Auxiliary prime and roots.** A prime $\ell$ with $3 \le \ell$, $\ell \neq q$ and $\ell \nmid M'$; an element $\zeta_0 \in k_0$ that is a primitive $q\ell$-th root of unity; and an element $\varpi_t \in k_0$ lying in $A$ with $\varpi_t^{q^2-1} = q u$ for some unit $u$ of $A$.
--
--   **The finite layer.** An intermediate field $K_1$ of $\overline{\mathbb Q}/k_0$, finite over $k_0$, and a valuation subring $A_1 \subseteq K_1$ consisting exactly of the elements of $K_1$ lying in $A$, assumed to be a henselian discrete valuation ring.
--
--   **Conclusion.** With $\mathrm{fieldBar}\,q\,M'$ regarded as a $k_0$-algebra through $\overline{\mathbb Q}$, the assertion is the following. Let $F_0$ be an intermediate field of $\mathrm{fieldBar}\,q\,M'/k_0$ such that: the compositum of $F_0$ with the $k_0$-subfield generated by the image of $\overline{\mathbb Q}$ is all of $\mathrm{fieldBar}\,q\,M'$; $F_0$ is stable under $\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma$ for every $\zeta'$ and every $\gamma \in \Gamma_0(M')$; for every intermediate field $K'$ of $\overline{\mathbb Q}/k_0$ finite over $k_0$, every finite family $c_i \in \overline{\mathbb Q}$ that is linearly independent over $K'$ and every family $a_i$ of elements of the compositum of $F_0$ with the $k_0$-subfield generated by the image of $K'$, the relation $\sum_i c_i a_i = 0$ forces all $a_i = 0$; and $F_0$ contains every element of $\mathrm{fieldBar}\,q\,M'$ whose Laurent series lies in the range of $\mathrm{coeffEmb}_{\overline{\mathbb Q}}$, i.e. has rational coefficients. Write $T_1$ for the compositum of $F_0$ with the $k_0$-subfield of $\mathrm{fieldBar}\,q\,M'$ generated by the image of $K_1$. Let $T_1$ carry an $A_1$-algebra structure whose structure map, followed by the inclusion of $T_1$ into $\mathrm{fieldBar}\,q\,M'$, agrees on $A_1 \subseteq K_1 \subseteq \overline{\mathbb Q}$ with the inclusion of constants, and let $j_1 \in T_1$ be an element whose image in $\mathrm{fieldBar}\,q\,M'$ is the element of $\mathrm{modularFunctionFieldBar}\,M'$ given by $\mathrm{coeffEmb}_{\overline{\mathbb Q}}(\mathrm{jq})$, included via `hle`, and with $j_1 \neq 0$. Then there exists a ring homomorphism
--   $$\psi : \mathrm{chartAlgInf}(A_1, T_1, j_1) \longrightarrow A_1$$
--   from the pole chart algebra — the $A_1$-subalgebra of $T_1$ of elements integral over $A_1[j_1^{-1}]$ — such that:
--
--   1. $\psi$ is a retraction of the structure map, i.e. $\psi(\mathrm{algebraMap}_{A_1}(a)) = a$ for all $a \in A_1$;
--
--   2. $\psi(\mathrm{jInvChartInf}(A_1, T_1, j_1)) = 0$, i.e. $\psi$ kills $j_1^{-1}$;
--
--   3. every $b$ in the chart algebra has image in $\mathrm{fieldBar}\,q\,M'$ lying in $\mathrm{qIntegersBar}(\overline{\mathbb Q}, \mathrm{fieldBar}\,q\,M')$, that is, its $q$-expansion has non-negative order;
--
--   4. for every $b$ in the chart algebra, the coefficient of $q^0$ in the Laurent series of the image of $b$ equals the image of $\psi(b)$ in $\overline{\mathbb Q}$, so $\psi$ is the constant-term map;
--
--   5. for every $b$ in the chart algebra whose image in $\mathrm{fieldBar}\,q\,M'$ is a non-unit of $R.\mathrm{integers}$, the element $\psi(b)$ lies in the maximal ideal of $A_1$.
--
--   This is the section of the cusp $\infty$ on the two-chart integral model over $A_1$: the pole chart algebra of $j_1^{-1}$ consists of $q$-expansions with coefficients integral at the cusp, so that taking the constant term is a ring homomorphism to $A_1$ which kills $j_1^{-1}$ and carries non-units of the Gauss ring at $\infty$ into the maximal ideal. It is used in the construction of places centred at the closed points of the special fibre lying on the $\infty$-Igusa component, via [`ModularCurve.FullLevel.exists_centred_of_toValuationSubring_eq_qIntegersBar_twoChartIntegralModel`](thm.html#ModularCurve.FullLevel.exists_centred_of_toValuationSubring_eq_qIntegersBar_twoChartIntegralModel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_constantTerm_chartAlgInf_twoChartIntegralModel_levelField.lean

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

theorem ModularCurve.FullLevel.exists_constantTerm_chartAlgInf_twoChartIntegralModel_levelField
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
    ∃ ψ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) →+* ↥A₁,
      (∀ a : ↥A₁, ψ (algebraMap ↥A₁ ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) a) = a) ∧
      ψ (AlgebraicCurve.TwoChartIntegralModel.jInvChartInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) = 0 ∧
      (∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁),
        ((b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ qIntegersBar (AlgebraicClosure ℚ) (fieldBar q M')) ∧
      (∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁),
        ((((b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ))).coeff 0 =
          (((ψ b : ↥A₁) : ↥K₁) : AlgebraicClosure ℚ)) ∧
      (∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁),
        ((b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ R.integers.nonunits → ψ b ∈ maximalIdeal ↥A₁) := by sorry
