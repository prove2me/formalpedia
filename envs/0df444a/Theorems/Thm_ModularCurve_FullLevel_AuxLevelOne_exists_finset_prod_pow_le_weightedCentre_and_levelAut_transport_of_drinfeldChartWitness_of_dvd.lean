-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_exists_finset_prod_pow_le_weightedCentre_and_levelAut_transport_of_drinfeldChartWitness_of_dvd
-- name    : ModularCurve.FullLevel.AuxLevelOne.exists_finset_prod_pow_le_weightedCentre_and_levelAut_transport_of_drinfeldChartWitness_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:14.444979+00:00
-- url     : https://prove2.me/theorems/0f408734-8bb9-5647-b0f4-6d0273a659c4
-- title:
--   Tame exponent and finite orbit support of the weighted blow-up centre
-- statement:
--   Throughout, $q$ is a prime, $M'$ a non-zero natural number with $q \nmid M'$, and $\ell$ a prime with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$.
--
--   **Level and function field.** $L$ is a field of characteristic zero, $\zeta \in L$ a primitive $q$-th root of unity, and `hι` asserts the existence of a ring homomorphism $\iota : L \to \mathbb{C}$ with $\iota(\zeta) = e^{2\pi i/q}$. The subgroup $H_1 \le (\mathbb{Z}/q^2M')^\times$ is required by `hH₁` to equal [`ModularCurve.FullLevel.levelH q M'`](def/ModularCurve_FullLevelJacobian.html#L22) intersected with the kernel of the reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/\ell)^\times$; here `levelH q M'` is the kernel of the reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$, so $H_1$ consists of the units congruent to $1$ modulo $q$ and modulo $\ell$. The intermediate field $K$ of the Laurent series field $\mathrm{LaurentSeries}(L)$ over $L$ is required by `hK` to be [`ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField (q ^ 2 * M') H₁)`](def/ModularCurve_LaurentCoeff.html#L103), i.e. the subfield generated over $L$ by the coefficientwise image under $\mathbb{Q} \to L$ of the $q$-expansion function field attached to the congruence subgroup [`CohCarrier.GammaH (q ^ 2 * M') H₁`](def/CohCarrier_Level.html#L133) of level $q^2M'$.
--
--   **Base ring and chart algebra.** $A$ is a henselian discrete valuation domain with algebraically closed residue field, with $L$ as its fraction field, such that $q$ lies in the maximal ideal of $A$ and $\zeta$ lies in the image of $A$ in $L$ (`hAq`, `hζA`); $K$ is an $A$-algebra compatibly with $L$. The element $j \in K$ is non-zero and its Laurent series is the coefficientwise image in $L$ of [`ModularCurve.jq`](def/ModularCurve_X0.html#L157), the $q$-expansion $q^{-1}\cdot(\text{integral } j\text{-numerator})$ of the modular $j$-invariant (`hj`). The element $\varpi \in A$ generates the maximal ideal (`hϖ`), and $\varpi_t \in A$ satisfies $\varpi_t^{\,q^2-1} = q\,u$ for some unit $u$ (`hϖt`). Write $C :=$ `chartAlgFin A K j`, the $A$-subalgebra of $K$ of elements integral over $A[j]$, and `jChartFin A K j` for $j$ regarded as an element of $C$.
--
--   **Supersingular point.** $y$ is a maximal ideal of $C$ containing $\varpi$ (`hy`, `hϖy`), and `hss` requires $y$ to be supersingular in the following sense: for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi : C \to \Omega$ with kernel $y$, the element $\varphi(j)$ lies in [`ModularCurve.ssJSet q Ω`](def/ModularCurve_SupersingularModuli.html#L7), that is, every elliptic Weierstrass curve over $\Omega$ with $j$-invariant $\varphi(j)$ has no non-zero point killed by $q$.
--
--   **The integral model.** $X :=$ [`AlgebraicCurve.TwoChartIntegralModel A K j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) is the pushout of the two maps $\mathrm{Spec}$ of the finite and infinite chart algebras along the middle chart, with structure morphism `toBase` to $\mathrm{Spec}\,A$. The point $z \in X$ is such that the germ at $z$ of the global section of $X$ obtained from $\varpi$ along `toBase` — this germ is the element $\varpi_z$ fixed by `hϖz` — lies in the maximal ideal of the stalk $\mathcal{O}_{X,z}$ (`hz`). The point $y'$ of `XFin A K j` $= \mathrm{Spec}\,C$ maps to $z$ under `ιFin` (`hy'`), satisfies the same supersingularity condition for its ideal (`hss'`), and `hy'y` identifies $y'.\mathrm{asIdeal}$ with $y$.
--
--   **Drinfeld chart datum.** $W_1$ is a complete discrete valuation domain, $\sigma_1 : A \to W_1$ a ring homomorphism carrying $\varpi$ to a generator of the maximal ideal of $W_1$ (`hσ₁`), and $f_1, u_1, v_1 \in W_1[[X_0,X_1]]$ with $u_1, v_1$ units and $f_1 \equiv X_0X_1^q - X_0^qX_1$ modulo $(X_0,X_1)^{q+2}$ (`hf₁`, the congruence being against [`DrinfeldCurve.LocalChart.drinfeldForm q W₁`](def/DrinfeldCurve_LocalChart.html#L18)). Finally $e_1$ is a ring isomorphism from the adic completion of $\mathcal{O}_{X,z}$ with respect to its maximal ideal onto
--   $$S := W_1[[X_0,X_1]]\big/\big(C(\sigma_1(\varpi_t^{\,q+1}))\,v_1 - f_1u_1\big).$$
--   Throughout the statement the following abbreviations are introduced by `let`: $\mathrm{STK} = \mathcal{O}_{X,z}$, $\mathrm{CMP}$ its adic completion, $\mathrm{toC} : \mathrm{STK} \to \mathrm{CMP}$ the completion map, $\mathrm{mkS} : W_1[[X_0,X_1]] \to S$ the quotient map, and $\mathrm{germY} : C \to \mathrm{STK}$ the germ homomorphism at $z$ obtained from the global sections of $\mathrm{Spec}\,C$ through the open immersion `ιFin`. Write $\Psi := e_1 \circ \mathrm{toC} \circ \mathrm{germY} : C \to S$ and
--   $$J_y := \Psi^{-1}\big(\big(\mathrm{mkS}\,C(\sigma_1\varpi_t),\ \mathrm{mkS}\,X_0,\ \mathrm{mkS}\,X_1\big)\big).$$
--
--   The hypothesis `hW₁` is a conjunction of seven clauses on this datum, summarised here: (i) $e_1$ carries the image in $\mathrm{CMP}$ of the germ of any $a \in A$ to the class of $C(\sigma_1 a)$; (ii) for $\gamma \in \Gamma_0(M')$, any $\tau \in \mathrm{Aut}_L(K)$ satisfying [`ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ`](def/ModularCurve_FullLevelLevelAutAt.html#L29) maps $C$ into $C$; (iii) if moreover $\gamma_{11} \equiv 1 \pmod{\ell}$, the induced endomorphism of $C$ is congruent to the identity modulo $y$; (iv) for $\gamma \in \Gamma_0(M')$ and such a $\tau$ congruent to the identity modulo $y$ there are a ring automorphism $\theta$ of $S$, an element $c \in W_1$ and a matrix $M \in M_2(W_1)$ with $\theta$ intertwining $\Psi$ with the action of $\tau$ on $C$, $\theta$ fixing the constants, $\theta(X_k) \equiv \sum_i M_{ik}X_i$ modulo the square of the ideal generated by the classes of $X_0,X_1$, $c^{q+1} \equiv 1$ and $M \equiv c\,\gamma$ entrywise modulo the maximal ideal of $W_1$, together with $c \equiv 1$ when $\gamma_{11} \equiv 1 \pmod{\ell}$, and $c \not\equiv 1$ when $\gamma \in \Gamma(q)$ and $\tau \neq \mathrm{id}$; (v) two primes of $S$ containing the class of $C(\sigma_1\varpi)$, not containing both classes of $X_0,X_1$, and containing elements $a_iX_0 + b_iX_1$ modulo $(X_0,X_1)^2$ with $q \nmid a_1b_2 - a_2b_1$, have distinct contractions along $e_1 \circ \mathrm{toC}$; (vi) for a prime $P$ of $S$ with those conditions and containing $X_0$ modulo $(X_0,X_1)^2$, an element $a \in C$ satisfies $\mathrm{toC}(\mathrm{germY}\,a) \in (e_1)^{-1}(P)$ if and only if every Laurent coefficient of $a$ lies in the image of the maximal ideal of $A$; (vii) an Igusa-type clause: [`ModularCurve.jqNModC L q`](def/ModularCurve_JqCoeff.html#L18), the $q$-fold $q$-expansion rescaling of the $j$-series, lies in $K$ and in $C$, and there are $a_0 \in A$ with the difference in $y$, an integer $e_0 \ge 1$ and $h \in (X_0,X_1)^{e_0}$ whose degree-$e_0$ form is a unit at every pair $(a,b)$ in $W_1$ with one entry a unit and $a^qb - ab^q$ in the maximal ideal, such that $\Psi$ of that difference is the class of $h$. In clauses (ii)–(iv) the predicate `IsLevelAutAt` requires, for all weights $k$, all modular forms $f,g$ of weight $k$ for [`CohCarrier.GammaH (q ^ 2 * M') H₁`](def/CohCarrier_Level.html#L133) with integral $q$-expansions and $g \neq 0$, all $x \in K$ whose Laurent series is the image of $f/g$, and all $\iota : L \to \mathbb{C}$ with $\iota(\zeta) = e^{2\pi i/q}$, that the coefficientwise image of $\tau x$ under $\iota$ times the $q$-expansion of $g \mid_k \mathrm{conjElemN}\, q\, \gamma^{-1}$ equals the $q$-expansion of $f \mid_k \mathrm{conjElemN}\, q\, \gamma^{-1}$.
--
--   **Centre and blow-up chart.** The ideal $J$ of $C$ is required by `hJ` to be the infimum of all ideals of the form $\rho_\tau^{-1}(J_y)$, where $\rho_\tau$ is the restriction to $C$ of an automorphism $\tau$ of $K$ over $L$ with `IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ` for some $\gamma \in \Gamma(q) \cap \Gamma_0(M')$ preserving $C$. The subalgebra $B \le K$ over $A$ is required by `hB` to be the $C$-algebra generated by $\{x \in K : x\varpi_t \in J\}$, i.e. $B = C[J/\varpi_t]$.
--
--   **Conclusion.** Under these hypotheses six assertions hold simultaneously.
--
--   1. There is $m \ge 1$ with $(\varpi_t) = \mathfrak{m}_A^{\,m}$ and $y^m \subseteq J_y$.
--
--   2. For every $c \in y$ there is $a \in C$ with $c - \varpi a \in J_y$.
--
--   3. $J \subseteq J_y$.
--
--   4. $J_y \subseteq y$.
--
--   5. There is $i_1 \in C$ with $i_1 - 1 \in y$ such that for every $c \in y$ there is $b \in B$ with $c\,i_1 = \varpi\,b$ in $K$.
--
--   6. There are a finite set $T$ of ideals of $C$ and an integer $N \ge 1$ such that $y \in T$, every $P \in T$ is maximal, $\prod_{P \in T} P^N \subseteq J$, and every $P \in T$ is of the form $P = \rho_\tau^{-1}(y)$ for some $\gamma \in \Gamma(q) \cap \Gamma_0(M')$ and some automorphism $\tau$ of $K$ over $L$ satisfying `IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ` and mapping $C$ into $C$, with the additional properties that $\tau^{-1}$ maps $C$ into $C$ and that both $\tau$ and $\tau^{-1}$ map $B$ into $B$.
--
--   This is a structural step in the analysis of the two-chart integral model of the modular curve of level $q^2M'$ with unit group $H_1$ at a supersingular point, in the variant frame where the auxiliary rigidifying level is a diamond condition modulo a prime $\ell \equiv 11 \pmod{12}$ dividing $M'$, so that no lower bound on $q$ is needed. It records the tame exponent relating $\varpi_t$ to the maximal ideal of $A$, the decomposition $y = (\varpi) + J_y$ with $J_y \subseteq y$, the containment $J \subseteq J_y$ for the weighted centre $J$, a principalisation statement for $y$ in the blow-up chart $B = C[J/\varpi_t]$, and the finiteness of the orbit of maximal ideals supporting $J$ together with the stability of $C$ and $B$ under the relevant level automorphisms. These conclusions are used by the subsequent lemmas of the same development that compare contractions of the Drinfeld chart ideals along the orbit and extract units in the centre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevelOne_exists_finset_prod_pow_le_weightedCentre_and_levelAut_transport_of_drinfeldChartWitness_of_dvd.lean

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

theorem ModularCurve.FullLevel.AuxLevelOne.exists_finset_prod_pow_le_weightedCentre_and_levelAut_transport_of_drinfeldChartWitness_of_dvd
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
              algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a₀))) = mkS h))

    (J : Ideal ↥(chartAlgFin A (↥K) j))
    (hJ :
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
        J = sInf {J' : Ideal ↥(chartAlgFin A (↥K) j) | ∃ (γ : SL(2, ℤ)) (_ : γ ∈ CongruenceSubgroup.Gamma q)
          (_ : γ ∈ CongruenceSubgroup.Gamma0 M') (τ : ↥K ≃ₐ[L] ↥K)
          (_ : ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ)
          (hpres : ∀ a : ↥K, a ∈ chartAlgFin A (↥K) j → τ a ∈ chartAlgFin A (↥K) j),
          J' = Ideal.comap ((τ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpres)
            (Ideal.comap ((e₁ : CMP →+* S).comp (toC.comp germY))
              (Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖt)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}))})

    (B : Subalgebra A ↥K)
    (hB : B = (Algebra.adjoin ↥(chartAlgFin A (↥K) j)
        {x : ↥K | ∃ i ∈ J, x * algebraMap A ↥K ϖt = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}).restrictScalars A) :
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

        (∃ m : ℕ, 1 ≤ m ∧ Ideal.span {ϖt} = IsLocalRing.maximalIdeal A ^ m ∧
          y ^ m ≤ Ideal.comap ((e₁ : CMP →+* S).comp (toC.comp germY))
            (Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖt)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)})) ∧

        (∀ c : ↥(chartAlgFin A (↥K) j), c ∈ y → ∃ a : ↥(chartAlgFin A (↥K) j),
            c - algebraMap A ↥(chartAlgFin A (↥K) j) ϖ * a ∈ Ideal.comap ((e₁ : CMP →+* S).comp (toC.comp germY))
              (Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖt)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)})) ∧

        J ≤ Ideal.comap ((e₁ : CMP →+* S).comp (toC.comp germY))
              (Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖt)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ∧
        Ideal.comap ((e₁ : CMP →+* S).comp (toC.comp germY))
              (Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖt)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ≤ y ∧

        (∃ i₁ : ↥(chartAlgFin A (↥K) j), i₁ - 1 ∈ y ∧
            ∀ c : ↥(chartAlgFin A (↥K) j), c ∈ y → ∃ b : ↥B, (c : ↥K) * (i₁ : ↥K) = algebraMap A ↥K ϖ * (b : ↥K)) ∧

        (∃ (T : Finset (Ideal ↥(chartAlgFin A (↥K) j))) (N : ℕ), 1 ≤ N ∧ y ∈ T ∧ (∀ P ∈ T, P.IsMaximal) ∧
            (∏ P ∈ T, P ^ N) ≤ J ∧
            (∀ P ∈ T, ∃ (γ : SL(2, ℤ)) (_ : γ ∈ CongruenceSubgroup.Gamma q) (_ : γ ∈ CongruenceSubgroup.Gamma0 M')
                (τ : ↥K ≃ₐ[L] ↥K)
                (_ : ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ)
                (hpres : ∀ a : ↥K, a ∈ chartAlgFin A (↥K) j → τ a ∈ chartAlgFin A (↥K) j),
                (∀ a : ↥K, a ∈ chartAlgFin A (↥K) j → τ.symm a ∈ chartAlgFin A (↥K) j) ∧
                (∀ f : ↥K, f ∈ B → τ f ∈ B) ∧ (∀ f : ↥K, f ∈ B → τ.symm f ∈ B) ∧
                P = Ideal.comap ((τ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpres) y)) := by sorry
