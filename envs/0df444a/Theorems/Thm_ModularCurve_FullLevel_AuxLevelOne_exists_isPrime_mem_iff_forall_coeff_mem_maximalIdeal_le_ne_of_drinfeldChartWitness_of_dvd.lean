-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_exists_isPrime_mem_iff_forall_coeff_mem_maximalIdeal_le_ne_of_drinfeldChartWitness_of_dvd
-- name    : ModularCurve.FullLevel.AuxLevelOne.exists_isPrime_mem_iff_forall_coeff_mem_maximalIdeal_le_ne_of_drinfeldChartWitness_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:14.444979+00:00
-- url     : https://prove2.me/theorems/25a71041-b778-565d-b9d8-5432d4395052
-- title:
--   Gauss ideal is prime and strictly below a supersingular point
-- statement:
--   **Data.** Let $q$ and $\ell$ be primes and $M'$ a nonzero natural number with $q \nmid M'$, together with the guard conditions $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$. Let $L$ be a field of characteristic $0$, let $\zeta \in L$ be a primitive $q$-th root of unity, and assume (`hι`) that there is a ring homomorphism $\iota : L \to \mathbb{C}$ with $\iota(\zeta) = e^{2\pi i/q}$.
--
--   **Level and function field.** $H_1$ is the subgroup of $(\mathbb{Z}/q^2M')^\times$ equal to the intersection of [`ModularCurve.FullLevel.levelH q M'`](def/ModularCurve_FullLevelJacobian.html#L22), the kernel of the reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$, with the kernel of the reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/\ell)^\times$; thus $H_1$ consists of the units that are $\equiv 1$ modulo $q$ and modulo $\ell$. $K$ is the intermediate field of $L \subseteq L((t))$ obtained by [`ModularCurve.laurentBaseChange`](def/ModularCurve_LaurentCoeff.html#L103), i.e. generated over $L$ by the image under the coefficientwise map [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81) of the $q$-expansion function field [`ModularCurve.xHFunctionField (q^2*M') H₁`](def/ModularCurve_XH.html#L79) of the modular curve of level $\Gamma_{H_1}(q^2M')$ over $\mathbb{Q}$.
--
--   **Valuation ring and the $j$-chart.** $A$ is a henselian discrete valuation domain with algebraically closed residue field, an $L$-algebra which is a fraction-ring realisation of $A$ (so $L$ is the fraction field of $A$), with $q \in \mathfrak{m}_A$ and $\zeta$ in the image of $A$ in $L$; $K$ carries an $A$-algebra structure compatible with that of $L$. The element $j \in K$ is nonzero and has Laurent expansion [`ModularCurve.coeffEmb L ModularCurve.jq`](def/ModularCurve_LaurentCoeff.html#L81), the rational $q$-expansion $t^{-1}\cdot(\text{power series }j\text{-numerator})$ of the modular $j$-function. Further, $\varpi$ generates $\mathfrak{m}_A$, and $\varpi_t \in A$ satisfies $\varpi_t^{\,q^2-1} = q u$ for some unit $u$ of $A$ (a tame uniformiser datum). Throughout, $C :=$ `chartAlgFin A K j` is the $j$-finite chart algebra, the subalgebra of elements of $K$ integral over $A[j]$, and `jChartFin A K j` is $j$ viewed in $C$.
--
--   **The supersingular point.** $y$ is a maximal ideal of $C$ containing the image of $\varpi$, and is supersingular in the following sense (`hss`): for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi : C \to \Omega$ with kernel $y$, the value $\varphi(j)$ lies in [`ModularCurve.ssJSet q Ω`](def/ModularCurve_SupersingularModuli.html#L7), the set of those $j_0 \in \Omega$ such that every elliptic curve over $\Omega$ with $j$-invariant $j_0$ has no nonzero $q$-torsion point.
--
--   **The point of the two-chart model.** $X :=$ [`AlgebraicCurve.TwoChartIntegralModel A K j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) is the pushout of the two maps from the middle chart to $\operatorname{Spec}$ of the $j$-finite and $j^{-1}$-finite chart algebras, and `toBase` is its structure morphism to $\operatorname{Spec} A$. The data consist of a point $z$ of $X$, the germ $\varpi_z$ at $z$ of the global section of $X$ obtained from $\varpi$ along `toBase`, the hypothesis that $\varpi_z$ lies in the maximal ideal of the stalk $\mathcal{O}_{X,z}$, a point $y'$ of `XFin A K j` $= \operatorname{Spec} C$ whose image under `ιFin` is $z$, the same supersingularity hypothesis (`hss'`) for the prime $y'.\mathrm{asIdeal}$, and the identification $y'.\mathrm{asIdeal} = y$.
--
--   **The Drinfeld-chart witness.** $W_1$ is a complete (adically complete for its maximal ideal) discrete valuation domain, $\sigma_1 : A \to W_1$ a ring homomorphism with $\mathfrak{m}_{W_1} = (\sigma_1 \varpi)$, and $f_1, u_1, v_1 \in W_1[[X_0,X_1]]$ with $u_1, v_1$ units and $f_1 \equiv$ [`DrinfeldCurve.LocalChart.drinfeldForm q W₁`](def/DrinfeldCurve_LocalChart.html#L18) $= X_0X_1^q - X_0^qX_1 \pmod{(X_0,X_1)^{q+2}}$.
--   Finally $e_1$ is a ring isomorphism from the $\mathfrak{m}$-adic completion $\mathrm{CMP}$ of $\mathcal{O}_{X,z}$ onto
--   $$S := W_1[[X_0,X_1]]\big/\big(C(\sigma_1(\varpi_t^{\,q+1}))\,v_1 - f_1u_1\big),$$
--   with $\mathrm{mkS}$ the quotient map, $\mathrm{toC} : \mathcal{O}_{X,z} \to \mathrm{CMP}$ the completion map, and $\mathrm{germY} : C \to \mathcal{O}_{X,z}$ the canonical map obtained from the identification of the sections of $X$ over the open set `ιFin ''ᵁ ⊤` with $C$ followed by the germ at $z$.
--
--   **The compatibility package `hW₁`** is a conjunction of seven clauses, namely:
--
--   (i) for every $a \in A$, $e_1$ carries the completed germ of the image of $a$ under `toBase` to $\mathrm{mkS}(C(\sigma_1 a))$;
--
--   (ii) for every $\gamma \in \Gamma_0(M')$ and every $L$-algebra automorphism $\tau$ of $K$ satisfying [`ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q^2*M') H₁ γ⁻¹ K τ`](def/ModularCurve_FullLevelLevelAutAt.html#L29), the automorphism $\tau$ maps $C$ into $C$. Here the predicate `IsLevelAutAt` asserts: for every weight $k$, all modular forms $f, g$ of weight $k$ for the subgroup of $\mathrm{GL}_2(\mathbb{R})$ attached to $\Gamma_{H_1}(q^2M')$ having integral $q$-expansions $p_f, p_g$ with the Laurent series of $p_g$ nonzero, every $x \in K$ whose Laurent expansion is the image under `coeffEmb` of $p_f/p_g$, and every ring homomorphism $\iota : L \to \mathbb{C}$ with $\iota(\zeta) = e^{2\pi i /q}$, one has $\iota_*\big(\tau x\big) \cdot \mathrm{qExp}(g\mid_k \mathrm{conjElemN}\,q\,\gamma^{-1}) = \mathrm{qExp}(f\mid_k \mathrm{conjElemN}\,q\,\gamma^{-1})$, where `conjElemN q δ` is the matrix $\begin{pmatrix} \delta_{00} & \delta_{01}/q \\ q\,\delta_{10} & \delta_{11}\end{pmatrix}$;
--
--   (iii) for $\gamma \in \Gamma_0(M')$ with $\gamma_{11} \equiv 1 \pmod{\ell}$ and $\tau$ as in (ii), preserving $C$, the induced endomorphism of $C$ is congruent to the identity modulo $y'.\mathrm{asIdeal}$, i.e. $\tau(a) - a \in y'.\mathrm{asIdeal}$ for all $a \in C$;
--
--   (iv) for $\gamma \in \Gamma_0(M')$ and $\tau$ as in (ii) preserving $C$ and congruent to the identity modulo $y'.\mathrm{asIdeal}$, there exist a ring automorphism $\theta$ of $S$, an element $c \in W_1$ and a matrix $M \in \mathrm{M}_2(W_1)$ such that: $\theta$ intertwines $e_1 \circ \mathrm{toC} \circ \mathrm{germY}$ with the same map composed with the restriction of $\tau$; $\theta$ fixes the image of every constant $C(w)$, $w \in W_1$; for each $j \in \{0,1\}$, $\theta(\mathrm{mkS}(X_j)) - \mathrm{mkS}\big(\sum_i C(M_{ij})X_i\big)$ lies in the square of the ideal generated by the images of $X_0, X_1$; $c^{q+1} \equiv 1$ modulo $\mathfrak{m}_{W_1}$; $M_{ij} \equiv c\,\gamma_{ij}$ modulo $\mathfrak{m}_{W_1}$ for all $i,j$; if $\gamma_{11} \equiv 1 \pmod{\ell}$ then $c \equiv 1$ modulo $\mathfrak{m}_{W_1}$; and if $\gamma \in \Gamma(q)$ and $\tau$ is not the identity on $K$ then $c - 1 \notin \mathfrak{m}_{W_1}$;
--
--   (v) a separation clause for branch primes: for all integers $a_1,b_1,a_2,b_2$ and all primes $P_1, P_2$ of $S$ such that each $P_i$ omits at least one of $\mathrm{mkS}(X_0), \mathrm{mkS}(X_1)$, each contains $\mathrm{mkS}(C(\sigma_1\varpi))$, and each contains an element $\mathrm{mkS}(C(a_i)X_0 + C(b_i)X_1 + h)$ with $h \in (X_0,X_1)^2$, if $q \nmid a_1b_2 - a_2b_1$ then the contractions of $P_1$ and $P_2$ along $e_1 \circ \mathrm{toC}$ are distinct;
--
--   (vi) a description of one branch by coefficients: for every prime $P$ of $S$ omitting at least one of $\mathrm{mkS}(X_0), \mathrm{mkS}(X_1)$, containing $\mathrm{mkS}(C(\sigma_1\varpi))$, and containing an element $\mathrm{mkS}(C(1)X_0 + C(0)X_1 + h)$ with $h \in (X_0,X_1)^2$, and for every $a \in C$: $\mathrm{toC}(\mathrm{germY}(a))$ lies in the contraction of $P$ along $e_1$ if and only if every Laurent coefficient of $a$ (as an element of $K \subseteq L((t))$) lies in the image of $\mathfrak{m}_A$ under $A \to L$;
--
--   (vii) a clause about the $q$-expansion $j_{q,N}$ given by [`ModularCurve.jqNModC L q`](def/ModularCurve_JqCoeff.html#L18): there exist a proof that $j_{q,N} \in K$, a proof that the resulting element of $K$ lies in $C$, an element $a_0 \in A$ with $j_{q,N} - a_0 \in y'.\mathrm{asIdeal}$ in $C$, an integer $e_0 \ge 1$ and $h \in (X_0,X_1)^{e_0} \subseteq W_1[[X_0,X_1]]$ such that (a) for all $a, b \in W_1$ not both in $\mathfrak{m}_{W_1}$ with $a^qb - ab^q \in \mathfrak{m}_{W_1}$, the value $\sum_{i=0}^{e_0} \mathrm{coeff}_{(i,\,e_0-i)}(h)\,a^i b^{\,e_0-i}$ of the degree-$e_0$ leading form of $h$ is a unit of $W_1$, and (b) $e_1\big(\mathrm{toC}(\mathrm{germY}(j_{q,N} - a_0))\big) = \mathrm{mkS}(h)$.
--
--   **Conclusion.** Under these hypotheses there exists an ideal $G$ of the $j$-finite chart algebra $C =$ `chartAlgFin A K j` such that:
--
--   1. $G$ is prime;
--
--   2. for every $a \in C$, one has $a \in G$ if and only if for every $n \in \mathbb{Z}$ the $n$-th Laurent coefficient of $a$, viewed in $L((t))$, lies in the image of $\mathfrak{m}_A$ under $A \to L$ (that is, $G$ is exactly the set of elements all of whose $q$-expansion coefficients are non-units of $A$);
--
--   3. the image of $\varpi$ under $A \to C$ lies in $G$;
--
--   4. $G \le y$;
--
--   5. $G \ne y$.
--
--   This is the Gauss-valuation (coefficientwise) prime of the $j$-finite chart algebra of the modular curve of level $\Gamma_{H_1}(q^2M')$, exhibited as a prime strictly contained in a given supersingular maximal ideal $y$ of characteristic $q$; the hypotheses package the local structure of the two-chart integral model at the corresponding point as a Drinfeld-type plane quotient $W_1[[X_0,X_1]]/(\varpi_t^{q+1}v_1 - f_1u_1)$ with $f_1$ congruent to $X_0X_1^q - X_0^qX_1$ to high order. It is the variant of the construction adapted to small $q$ by a diamond condition at a guard prime $\ell \equiv 11 \pmod{12}$ dividing $M'$, and it feeds the subsequent analysis of the blow-up chart and of the coefficient criterion for level automorphisms in $\Gamma(q)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevelOne_exists_isPrime_mem_iff_forall_coeff_mem_maximalIdeal_le_ne_of_drinfeldChartWitness_of_dvd.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_CoordRing
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory AlgebraicGeometry IsLocalRing AlgebraicCurve.TwoChartIntegralModel

open scoped MatrixGroups

theorem ModularCurve.FullLevel.AuxLevelOne.exists_isPrime_mem_iff_forall_coeff_mem_maximalIdeal_le_ne_of_drinfeldChartWitness_of_dvd
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')

    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)

    (hι : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / q))
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [HenselianLocalRing A] [IsAlgClosed (ResidueField A)]
    (hAq : (q : A) ∈ maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ})

    (ϖt : A) (hϖt : ∃ u : A, IsUnit u ∧ ϖt ^ (q ^ 2 - 1) = (q : A) * u)

    (y : Ideal ↥(chartAlgFin A (↥K) j)) (hy : y.IsMaximal) (hϖy : algebraMap A ↥(chartAlgFin A (↥K) j) ϖ ∈ y)
    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(chartAlgFin A (↥K) j) →+* Ω), RingHom.ker φ = y → φ (jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω)
    (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j))
        (ϖz : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
        (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
          (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
        (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        (y' : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j))
        (hy' : (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y' = z)
        (hss' : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
          (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω),
          RingHom.ker φ = y'.asIdeal →
            φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω)
    (hy'y : y'.asIdeal = y)
      (W₁ : Type) [CommRing W₁] [IsDomain W₁] [IsDiscreteValuationRing W₁]
        [IsAdicComplete (IsLocalRing.maximalIdeal W₁) W₁] (σ₁ : A →+* W₁)
        (hσ₁ : IsLocalRing.maximalIdeal W₁ = Ideal.span {σ₁ ϖ})
        (f₁ u₁ v₁ : MvPowerSeries (Fin 2) W₁) (hu₁ : IsUnit u₁) (hv₁ : IsUnit v₁)
        (hf₁ : f₁ - DrinfeldCurve.LocalChart.drinfeldForm q W₁ ∈
          (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ (q + 2))
        (e₁ : AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ≃+*
          MvPowerSeries (Fin 2) W₁ ⧸ Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})

    (hW₁ :
        let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
        let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        let toC : STK →+* CMP := algebraMap STK CMP
        let S := (MvPowerSeries (Fin 2) W₁ ⧸ Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
        let mkS : MvPowerSeries (Fin 2) W₁ →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
        let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
          ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
              ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y', trivial, hy'⟩).hom.comp
            ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
              (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)

        (∀ a : A, e₁ (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
              (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
            (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
              (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
                ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)))) =
          Ideal.Quotient.mk _ (MvPowerSeries.C (σ₁ a))) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
            ∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
              τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' → ((γ 1 1 : ℤ) : ZMod ℓ) = 1 →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
            ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
                τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
              ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y'.asIdeal) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
            ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
                τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
              (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y'.asIdeal) →
                ∃ (θ : S ≃+* S) (c : W₁) (M : Matrix (Fin 2) (Fin 2) W₁),

                  (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                    θ (e₁ (toC (germY a))) = e₁ (toC (germY (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a)))) ∧

                  (∀ w : W₁, θ (mkS (MvPowerSeries.C w)) = mkS (MvPowerSeries.C w)) ∧

                  (∀ jj : Fin 2, θ (mkS (MvPowerSeries.X jj)) -
                      mkS (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) ∈
                    (Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2) ∧
                  (c ^ (q + 1) - 1 ∈ IsLocalRing.maximalIdeal W₁) ∧
                  (∀ ii jj : Fin 2, M ii jj - c * ((γ ii jj : ℤ) : W₁) ∈ IsLocalRing.maximalIdeal W₁) ∧
                  (((γ 1 1 : ℤ) : ZMod ℓ) = 1 → c - 1 ∈ IsLocalRing.maximalIdeal W₁) ∧

                  (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥K, τ k = k) → c - 1 ∉ IsLocalRing.maximalIdeal W₁)) ∧

        (∀ (a₁ b₁ a₂ b₂ : ℤ) (P₁ P₂ : Ideal S), P₁.IsPrime → P₂.IsPrime →

          (mkS (MvPowerSeries.X 0) ∉ P₁ ∨ mkS (MvPowerSeries.X 1) ∉ P₁) →
          (mkS (MvPowerSeries.X 0) ∉ P₂ ∨ mkS (MvPowerSeries.X 1) ∉ P₂) →
          mkS (MvPowerSeries.C (σ₁ ϖ)) ∈ P₁ → mkS (MvPowerSeries.C (σ₁ ϖ)) ∈ P₂ →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C ((a₁ : ℤ) : W₁) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₁ : ℤ) : W₁) * MvPowerSeries.X 1 + h)
                ∈ P₁) →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C ((a₂ : ℤ) : W₁) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₂ : ℤ) : W₁) * MvPowerSeries.X 1 + h)
                ∈ P₂) →
          ¬ ((q : ℤ) ∣ a₁ * b₂ - a₂ * b₁) →
            Ideal.comap ((e₁ : CMP →+* S).comp toC) P₁ ≠ Ideal.comap ((e₁ : CMP →+* S).comp toC) P₂) ∧

        (∀ P : Ideal S, P.IsPrime → (mkS (MvPowerSeries.X 0) ∉ P ∨ mkS (MvPowerSeries.X 1) ∉ P) →
          mkS (MvPowerSeries.C (σ₁ ϖ)) ∈ P →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C (1 : W₁) * MvPowerSeries.X 0 + MvPowerSeries.C (0 : W₁) * MvPowerSeries.X 1 + h) ∈ P) →
          ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
            toC (germY a) ∈ Ideal.comap (e₁ : CMP →+* S) P ↔
              ∀ n : ℤ, ∃ m ∈ IsLocalRing.maximalIdeal A,
                (((a : ↥K) : LaurentSeries L).coeff n) = algebraMap A L m) ∧

        (∃ (hjK : ModularCurve.jqNModC L q ∈ K)
           (hjC : (⟨ModularCurve.jqNModC L q, hjK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
           (a₀ : A) (_ : (⟨(⟨ModularCurve.jqNModC L q, hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) -
              algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a₀ ∈ y'.asIdeal)
           (e₀ : ℕ) (_ : 1 ≤ e₀) (h : MvPowerSeries (Fin 2) W₁)
           (_ : h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ e₀),
           (∀ a b : W₁, (a ∉ IsLocalRing.maximalIdeal W₁ ∨ b ∉ IsLocalRing.maximalIdeal W₁) →
              a ^ q * b - a * b ^ q ∈ IsLocalRing.maximalIdeal W₁ →
              IsUnit (∑ i ∈ Finset.range (e₀ + 1),
                MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (e₀ - i)) h * a ^ i * b ^ (e₀ - i))) ∧
           (e₁ : CMP →+* S) (toC (germY ((⟨(⟨ModularCurve.jqNModC L q, hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) -
              algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a₀))) = mkS h)) :
    ∃ G : Ideal ↥(chartAlgFin A (↥K) j), G.IsPrime ∧
      (∀ a : ↥(chartAlgFin A (↥K) j), a ∈ G ↔ (∀ n : ℤ, ∃ m ∈ IsLocalRing.maximalIdeal A, (((a : ↥K) : LaurentSeries L).coeff n) = algebraMap A L m)) ∧
      algebraMap A ↥(chartAlgFin A (↥K) j) ϖ ∈ G ∧ G ≤ y ∧ G ≠ y := by sorry
