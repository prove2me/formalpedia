-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevel_finitePresentation_krullDimLE_exists_exceptionalValuation_blowupChart_of_drinfeldChartWitness
-- name    : ModularCurve.FullLevel.AuxLevel.finitePresentation_krullDimLE_exists_exceptionalValuation_blowupChart_of_drinfeldChartWitness
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:22.181174+00:00
-- url     : https://prove2.me/theorems/68940dcd-cb61-50e8-9ad2-6b589b93a848
-- title:
--   Weighted blow-up chart C[J/varpiₜ]: presentation, fibre dimension, exceptional valuation
-- statement:
--   Throughout, $q$ is a prime with $q \ge 5$, $M'$ a non-zero natural number with $q \nmid M'$, and $\ell$ a prime with $\ell \ge 3$, $\ell \ne q$ and $\ell \nmid M'$. Further, $L$ is a field of characteristic zero, $\xi \in L$ is a primitive $(q\ell)$-th root of unity (`hξ`), and `hι` provides a ring homomorphism $\iota : L \to \mathbb{C}$ with $\iota(\xi) = e^{2\pi i/(q\ell)}$. The field $K$ is an intermediate field of $L \subseteq L(\!(T)\!)$ which by `hK` is [`ModularCurve.laurentBaseChange L`](def/ModularCurve_LaurentCoeff.html#L103) applied to the $q$-expansion function field [`ModularCurve.xHFunctionField ((q*ℓ)^2*M') (ModularCurve.FullLevel.levelH (q*ℓ) M')`](def/ModularCurve_XH.html#L79): that is, $K$ is generated over $L$ inside $L(\!(T)\!)$ by the coefficientwise image under [`ModularCurve.coeffEmb`](def/ModularCurve_LaurentCoeff.html#L81) of the function field of level $N_0 = (q\ell)^2M'$ attached to the subgroup $H = \ker\big((\mathbb{Z}/N_0)^\times \to (\mathbb{Z}/q\ell)^\times\big)$ of units congruent to $1$ modulo $q\ell$.
--
--   The coefficient ring $A$ is a Henselian discrete valuation ring with algebraically closed residue field, a domain with fraction field $L$, with $q \in \mathfrak m_A$ (`hAq`) and $\xi$ in the image of $A \to L$ (`hξA`); $K$ is an $A$-algebra compatibly with $A \to L \to K$. The element $j \in K$ is non-zero and, by `hj`, has Laurent series the image under [`ModularCurve.coeffEmb`](def/ModularCurve_LaurentCoeff.html#L81) of the modular $j$-series [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) over $\mathbb{Q}$. A uniformiser $\varpi$ generates $\mathfrak m_A$ (`hϖ`), and $\varpi_t \in A$ satisfies $\varpi_t^{\,q^2-1} = qu$ for some unit $u$ (`hϖt`).
--
--   Write $C =$ `chartAlgFin A K j` for the $j$-finite chart algebra, i.e. the $A$-subalgebra of $K$ of elements integral over $A[j]$, with distinguished element `jChartFin A K j` $= j$. The ideal $y \subseteq C$ is maximal (`hy`) and contains the image of $\varpi$ (`hϖy`); the hypothesis `hss` requires that for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi : C \to \Omega$ with kernel $y$, the value $\varphi(j)$ lies in [`ModularCurve.ssJSet q Ω`](def/ModularCurve_SupersingularModuli.html#L7), the set of elements $j_0$ such that every elliptic curve over $\Omega$ with $j$-invariant $j_0$ has no non-zero point killed by $q$.
--
--   On the geometric side, $X =$ [`AlgebraicCurve.TwoChartIntegralModel A K j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) is the scheme obtained as the pushout of the two maps from the middle chart to $\operatorname{Spec}$ of the $j$-finite and the $j^{-1}$-finite chart algebras, equipped with its structure morphism `toBase` to $\operatorname{Spec} A$. The point $z \in X$ is such that the germ $\varpi_z$ at $z$ of the global section of $X$ coming from $\varpi$ (`hϖz`) lies in the maximal ideal of the stalk $\mathcal{O}_{X,z}$ (`hz`). The point $y'$ of `XFin A K j` $= \operatorname{Spec} C$ maps to $z$ under `ιFin` (`hy'`), satisfies the same supersingularity condition `hss'` for its prime ideal, and `hy'y` identifies $y'.asIdeal$ with $y$.
--
--   The local presentation data consist of: a complete discrete valuation ring $W_1$ (a domain, adically complete for its maximal ideal), a ring homomorphism $\sigma_1 : A \to W_1$ with $\mathfrak m_{W_1} = (\sigma_1\varpi)$ (`hσ₁`), power series $f_1, u_1, v_1 \in W_1[\![X_0,X_1]\!]$ with $u_1, v_1$ units and $f_1 - (X_0X_1^q - X_0^qX_1) \in (X_0,X_1)^{q+2}$ (`hf₁`, the Drinfeld form [`DrinfeldCurve.LocalChart.drinfeldForm q W₁`](def/DrinfeldCurve_LocalChart.html#L18)), and a ring isomorphism $e_1$ from the adic completion of $\mathcal{O}_{X,z}$ at its maximal ideal onto
--   $$S = W_1[\![X_0,X_1]\!]\big/\big(C(\sigma_1(\varpi_t^{\,q+1}))\,v_1 - f_1u_1\big).$$
--   Writing `toC` for the completion map $\mathcal{O}_{X,z} \to \widehat{\mathcal{O}}_{X,z}$, `mkS` for the quotient map onto $S$ and `germY` for the composite of the canonical identification of $C$ with the sections of $X$ over the image of `ιFin` with the germ at $z$, the hypothesis `hW₁` is a conjunction of seven clauses: (i) $e_1$ carries the germ of each $a \in A$ to the class of the constant series $C(\sigma_1 a)$; (ii) for every $\gamma \in \Gamma_0(M')$ and every $\tau \in \operatorname{Aut}_L(K)$ with [`ModularCurve.FullLevel.IsLevelAutAt L (q*ℓ) ξ (q*ℓ) ((q*ℓ)^2*M') (levelH (q*ℓ) M') γ⁻¹ K τ`](def/ModularCurve_FullLevelLevelAutAt.html#L29) — that is, $\tau$ realises on $q$-expansions the substitution by the matrix `conjElemN (q*ℓ) γ⁻¹`, in the sense that for all weights $k$, all modular forms $f,g$ on the level group attached to $N_0$ and $H$ with integral $q$-expansions $p_f,p_g$, $p_g$ having non-zero image, all $x \in K$ whose Laurent series is the coefficient embedding of $p_f/p_g$, and all embeddings $\iota$ sending $\xi$ to $e^{2\pi i/(q\ell)}$, the series $\iota_*\tau(x)$ times the $q$-expansion of $g\mid_k \mathrm{conjElemN}(q\ell,\gamma^{-1})$ equals that of $f\mid_k \mathrm{conjElemN}(q\ell,\gamma^{-1})$ — such a $\tau$ maps $C$ into $C$; (iii) for $\gamma \in \Gamma_0(M') \cap \Gamma(\ell)$ and $\tau$ as in (ii) preserving $C$, the induced endomorphism of $C$ is the identity modulo $y'$; (iv) for $\gamma \in \Gamma_0(M')$ and $\tau$ as in (ii) preserving $C$ and inducing the identity modulo $y'$, there are a ring automorphism $\theta$ of $S$, an element $c \in W_1$ and a matrix $M \in M_2(W_1)$ such that $\theta$ intertwines the action of $\tau$ on $C$ through $e_1 \circ \mathrm{toC} \circ \mathrm{germY}$, fixes all constants $C(w)$, satisfies $\theta(X_j) \equiv \sum_i M_{ij}X_i$ modulo the square of the ideal generated by the classes of $X_0,X_1$, and has $c^{q+1} \equiv 1$ and $M_{ij} \equiv c\,\gamma_{ij}$ modulo $\mathfrak m_{W_1}$, with $c \equiv 1$ whenever $\gamma \in \Gamma(\ell)$ and $c \not\equiv 1$ whenever $\gamma \in \Gamma(q)$ and $\tau$ is not the identity; (v) two primes $P_1,P_2$ of $S$, each containing $C(\sigma_1\varpi)$, each omitting at least one of the classes of $X_0,X_1$, and each containing some element $a_iX_0 + b_iX_1 + h_i$ with $h_i \in (X_0,X_1)^2$ and integers $a_i,b_i$ with $q \nmid a_1b_2 - a_2b_1$, have distinct contractions along $e_1 \circ \mathrm{toC}$; (vi) for a prime $P$ of $S$ containing $C(\sigma_1\varpi)$, omitting at least one of the classes of $X_0,X_1$ and containing some $X_0 + h$ with $h \in (X_0,X_1)^2$, an element $a \in C$ has $\mathrm{toC}(\mathrm{germY}(a))$ in the contraction of $P$ along $e_1$ if and only if every Laurent coefficient of $a$ lies in the image of $\mathfrak m_A$; (vii) the series [`ModularCurve.jqNModC L (q*ℓ)`](def/ModularCurve_JqCoeff.html#L18), the $j$-series over $L$ with all exponents multiplied by $q\ell$, lies in $K$ and in $C$, and there are $a_0 \in A$ with this element congruent to $a_0$ modulo $y'$, an integer $e_0 \ge 1$ and $h \in (X_0,X_1)^{e_0}$ such that for all $a,b \in W_1$ not both in $\mathfrak m_{W_1}$ with $a^qb - ab^q \in \mathfrak m_{W_1}$ the element $\sum_{i=0}^{e_0} \mathrm{coeff}_{(i,e_0-i)}(h)\,a^ib^{e_0-i}$ is a unit, and $e_1(\mathrm{toC}(\mathrm{germY}(\mathrm{jqNModC} - a_0))) = \mathrm{mkS}(h)$.
--
--   Finally, the ideal $J \subseteq C$ is, by `hJ`, the infimum of the set of all ideals of $C$ of the form
--   $$J' = \big(\tau|_C\big)^{-1}\Big(\big(e_1 \circ \mathrm{toC} \circ \mathrm{germY}\big)^{-1}\big(\mathrm{mkS}(C(\sigma_1\varpi_t)),\ \mathrm{mkS}(X_0),\ \mathrm{mkS}(X_1)\big)\Big),$$
--   as $\gamma$ ranges over the elements of $\mathrm{SL}_2(\mathbb{Z})$ lying in $\Gamma(q) \cap \Gamma_0(M')$ and $\tau$ over the automorphisms of $K$ over $L$ that are level automorphisms at $\gamma^{-1}$ in the above sense and map $C$ into $C$. The $A$-subalgebra $B \subseteq K$ is, by `hB`, the restriction of scalars to $A$ of the $C$-algebra generated by $\{x \in K : x\varpi_t \in J\}$, i.e. the weighted blow-up chart $B = C[J/\varpi_t]$.
--
--   The conclusion is the conjunction of three assertions. First, $B$ is a finitely presented $A$-algebra. Second, the special fibre $B/\varpi B$ has Krull dimension at most $1$. Third, there exist a valuation subring $W$ of $K$ and a proof `hBW` that every element of $B$ lies in $W$, such that: an element of $L$ lies in $W$ if and only if it lies in the image of $A \to L$; the maximal ideal of $W$ is generated by the image of $\varpi$; $W$ is a discrete valuation ring; an element $b \in C$ lies in $y$ if and only if $b$ lies in $W$ and in $\mathfrak m_W$; and an element $f \in K$ lies in $W$ if and only if $fh = g$ for some $g,h \in B$ with $h \notin \mathfrak m_W$, so that $W$ is the localisation of $B$ at $\mathfrak m_W \cap B$.
--
--   This is the geometric analysis of the weighted blow-up of the $j$-finite chart of the two-chart integral model along the centre $J$ cut out by the Drinfeld-type local presentation at a supersingular point above $q$: it records that the resulting chart is of finite presentation over $A$, that its special fibre is at most one-dimensional, and that a prescribed discrete valuation of $K$, the exceptional valuation with centre $y$, is obtained as a localisation of the chart. It is used by [`ModularCurve.FullLevel.AuxLevel.exists_blowupChart_eq_adjoin_exceptionalValuation_of_drinfeldChartWitness_of_stalk_drinfeldChart_moduliHasse`](thm.html#ModularCurve.FullLevel.AuxLevel.exists_blowupChart_eq_adjoin_exceptionalValuation_of_drinfeldChartWitness_of_stalk_drinfeldChart_moduliHasse), where this conjunction is combined with the formal smoothness of the chart.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevel_finitePresentation_krullDimLE_exists_exceptionalValuation_blowupChart_of_drinfeldChartWitness.lean

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

theorem ModularCurve.FullLevel.AuxLevel.finitePresentation_krullDimLE_exists_exceptionalValuation_blowupChart_of_drinfeldChartWitness
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))

    (hι : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [HenselianLocalRing A] [IsAlgClosed (ResidueField A)]
    (hAq : (q : A) ∈ maximalIdeal A) (hξA : ∃ x : A, algebraMap A L x = ξ)
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
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            ∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
              τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' → γ ∈ CongruenceSubgroup.Gamma ℓ →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
                τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
              ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y'.asIdeal) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
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
                  (γ ∈ CongruenceSubgroup.Gamma ℓ → c - 1 ∈ IsLocalRing.maximalIdeal W₁) ∧

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

        (∃ (hjK : ModularCurve.jqNModC L (q * ℓ) ∈ K)
           (hjC : (⟨ModularCurve.jqNModC L (q * ℓ), hjK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
           (a₀ : A) (_ : (⟨(⟨ModularCurve.jqNModC L (q * ℓ), hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) -
              algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a₀ ∈ y'.asIdeal)
           (e₀ : ℕ) (_ : 1 ≤ e₀) (h : MvPowerSeries (Fin 2) W₁)
           (_ : h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ e₀),
           (∀ a b : W₁, (a ∉ IsLocalRing.maximalIdeal W₁ ∨ b ∉ IsLocalRing.maximalIdeal W₁) →
              a ^ q * b - a * b ^ q ∈ IsLocalRing.maximalIdeal W₁ →
              IsUnit (∑ i ∈ Finset.range (e₀ + 1),
                MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (e₀ - i)) h * a ^ i * b ^ (e₀ - i))) ∧
           (e₁ : CMP →+* S) (toC (germY ((⟨(⟨ModularCurve.jqNModC L (q * ℓ), hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) -
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
          (_ : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
            (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ)
          (hpres : ∀ a : ↥K, a ∈ chartAlgFin A (↥K) j → τ a ∈ chartAlgFin A (↥K) j),
          J' = Ideal.comap ((τ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpres)
            (Ideal.comap ((e₁ : CMP →+* S).comp (toC.comp germY))
              (Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖt)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}))})

    (B : Subalgebra A ↥K)
    (hB : B = (Algebra.adjoin ↥(chartAlgFin A (↥K) j)
        {x : ↥K | ∃ i ∈ J, x * algebraMap A ↥K ϖt = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}).restrictScalars A) :

        Algebra.FinitePresentation A ↥B ∧
        Ring.KrullDimLE 1 (↥B ⧸ Ideal.span {algebraMap A ↥B ϖ}) ∧

        ∃ (W : ValuationSubring ↥K) (hBW : ∀ f : ↥K, f ∈ B → f ∈ W),
          (∀ x : L, algebraMap L ↥K x ∈ W ↔ ∃ a : A, algebraMap A L a = x) ∧
          maximalIdeal ↥W = Ideal.span {(⟨algebraMap A ↥K ϖ, hBW _ (B.algebraMap_mem ϖ)⟩ : ↥W)} ∧
          IsDiscreteValuationRing ↥W ∧
          (∀ b : ↥(chartAlgFin A (↥K) j), b ∈ y ↔
            ∃ hb : (b : ↥K) ∈ W, (⟨(b : ↥K), hb⟩ : ↥W) ∈ maximalIdeal ↥W) ∧
          (∀ f : ↥K, f ∈ W ↔ ∃ g h : ↥B, (⟨(h : ↥K), hBW _ h.2⟩ : ↥W) ∉ maximalIdeal ↥W ∧ f * (h : ↥K) = (g : ↥K)) := by sorry
