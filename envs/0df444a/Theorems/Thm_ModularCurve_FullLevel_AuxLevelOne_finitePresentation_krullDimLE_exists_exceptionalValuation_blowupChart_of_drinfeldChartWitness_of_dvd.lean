-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_finitePresentation_krullDimLE_exists_exceptionalValuation_blowupChart_of_drinfeldChartWitness_of_dvd
-- name    : ModularCurve.FullLevel.AuxLevelOne.finitePresentation_krullDimLE_exists_exceptionalValuation_blowupChart_of_drinfeldChartWitness_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:14.444979+00:00
-- url     : https://prove2.me/theorems/fc03fb81-ae33-590d-9adc-edeb167ed355
-- title:
--   Blow-up chart C[J/varpiₜ]: presentation, fibre dimension, exceptional valuation
-- statement:
--   Arithmetic data. Fix a prime $q$ and a natural number $M' \neq 0$ with $q \nmid M'$, and a prime $\ell$ with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$. Let $L$ be a field of characteristic zero, $\zeta \in L$ a primitive $q$-th root of unity, and assume (`hι`) that there is a ring homomorphism $\iota : L \to \mathbb{C}$ with $\iota(\zeta) = e^{2\pi i/q}$. Let $H_1 \le (\mathbb{Z}/q^2M')^{\times}$ be the subgroup $\mathrm{levelH}\,q\,M' \cap \ker\big((\mathbb{Z}/q^2M')^{\times} \to (\mathbb{Z}/\ell)^{\times}\big)$, where [`ModularCurve.FullLevel.levelH q M'`](def/ModularCurve_FullLevelJacobian.html#L22) is the kernel of the reduction $(\mathbb{Z}/q^2M')^{\times} \to (\mathbb{Z}/q)^{\times}$; thus $H_1$ consists of the units congruent to $1$ modulo $q$ and modulo $\ell$. Let $K$ be the intermediate field of $L \subseteq L((\mathsf q))$ given by $K = \mathrm{laurentBaseChange}\,L\,(\mathrm{xHFunctionField}\,(q^2M')\,H_1)$, i.e. the subfield of the Laurent series field generated over $L$ by the image, under coefficientwise extension of scalars $\mathbb{Q}((\mathsf q)) \to L((\mathsf q))$, of the $q$-expansion function field of $\Gamma_{H_1}(q^2M')$.
--
--   Base ring and chart data. Let $A$ be a discrete valuation domain which is Henselian local with algebraically closed residue field, with $L$ as its fraction field, such that $q \in \mathfrak{m}_A$ and $\zeta$ lies in the image of $A \to L$; $K$ is an $A$-algebra compatibly with $L$. Let $j \in K$ be nonzero with Laurent expansion the image of [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) (the $q$-expansion $\mathsf q^{-1}+\dots$ of the modular invariant) under coefficientwise extension of scalars. Let $\varpi \in A$ generate $\mathfrak m_A$, and let $\varpi_t \in A$ satisfy $\varpi_t^{\,q^2-1} = q\,u$ for some unit $u$ of $A$. Write $C := \mathrm{chartAlgFin}\,A\,K\,j$ for the $A$-subalgebra of $K$ consisting of the elements integral over $A[j]$, and let $X := \mathrm{TwoChartIntegralModel}\,A\,K\,j$ be the two-chart integral model, the pushout of $\operatorname{Spec}$ of the two inclusions of the $j$-finite and $j^{-1}$-finite chart algebras into the middle algebra.
--
--   Supersingular centre. Let $y$ be a maximal ideal of $C$ containing the image of $\varpi$, such that (`hss`) for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi : C \to \Omega$ with kernel $y$, the value $\varphi(j)$ lies in [`ModularCurve.ssJSet q Ω`](def/ModularCurve_SupersingularModuli.html#L7), the set of those $j_0 \in \Omega$ for which every elliptic curve over $\Omega$ with $j$-invariant $j_0$ has no nonzero point killed by $q$. Let $z$ be a point of $X$ and let $\varpi_z$ be the germ at $z$ of the global section of $X$ obtained from $\varpi$ along the structure morphism $X \to \operatorname{Spec} A$; it is assumed that $\varpi_z$ lies in the maximal ideal of the stalk $\mathcal{O}_{X,z}$. Let $y'$ be a point of $\operatorname{Spec} C$ with image $z$ under the canonical morphism $\mathrm{ιFin}$, satisfying the same supersingularity condition (`hss'`) for homomorphisms out of $C$ with kernel $y'$, and assume $y' = y$ as ideals of $C$.
--
--   Drinfeld chart witness. Let $W_1$ be a discrete valuation domain, complete for its maximal-adic topology, $\sigma_1 : A \to W_1$ a ring homomorphism with $\mathfrak m_{W_1} = (\sigma_1\varpi)$, and $f_1, u_1, v_1 \in W_1[[X_0,X_1]]$ with $u_1, v_1$ units and $f_1 \equiv X_0X_1^{q} - X_0^{q}X_1 \pmod{(X_0,X_1)^{q+2}}$. Put $S := W_1[[X_0,X_1]]/\big(\sigma_1(\varpi_t^{\,q+1})v_1 - f_1u_1\big)$, write $\mathrm{mkS}$ for the quotient map, let $\widehat{\mathcal O}$ be the completion of $\mathcal{O}_{X,z}$ along its maximal ideal with $\mathrm{toC} : \mathcal{O}_{X,z} \to \widehat{\mathcal O}$ the canonical map, and let $e_1 : \widehat{\mathcal O} \xrightarrow{\ \sim\ } S$ be a ring isomorphism. Let $\mathrm{germY} : C \to \mathcal{O}_{X,z}$ be the germ map at $z$ through the open immersion $\mathrm{ιFin}$. The hypothesis `hW₁` is a conjunction of seven clauses: (i) $e_1 \circ \mathrm{toC}$ carries the germ at $z$ of the section determined by $a \in A$ to the class of the constant series $\sigma_1(a)$; (ii) for every $\gamma \in \Gamma_0(M')$ and every $L$-algebra automorphism $\tau$ of $K$ which is a level automorphism at $\gamma^{-1}$ in the sense of [`ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q^2*M') H₁ γ⁻¹ K τ`](def/ModularCurve_FullLevelLevelAutAt.html#L29) — that is, for all weights $k$ and all modular forms $f,g$ of weight $k$ on $\Gamma_{H_1}(q^2M')$ with integral $q$-expansions and $g \neq 0$, and every $x \in K$ whose Laurent expansion is the ratio of those expansions, the complex expansion of $\tau x$ times the $q$-expansion of $g|_k(\delta\gamma^{-1}\delta^{-1})$ equals that of $f|_k(\delta\gamma^{-1}\delta^{-1})$, with $\delta = \mathrm{diag}(1,q)$, measured through any $\iota : L \to \mathbb{C}$ sending $\zeta$ to $e^{2\pi i/q}$ — the automorphism $\tau$ maps $C$ into $C$; (iii) for $\gamma \in \Gamma_0(M')$ with $\gamma_{11} \equiv 1 \pmod{\ell}$ and $\tau$ a level automorphism at $\gamma^{-1}$ preserving $C$, one has $\tau(a) - a \in y'$ for all $a \in C$; (iv) for $\gamma \in \Gamma_0(M')$ and $\tau$ a level automorphism at $\gamma^{-1}$ preserving $C$ and satisfying $\tau(a)-a \in y'$ for all $a \in C$, there exist a ring automorphism $\theta$ of $S$, an element $c \in W_1$ and a matrix $M \in M_2(W_1)$ such that $\theta$ intertwines $\tau|_C$ with $e_1 \circ \mathrm{toC} \circ \mathrm{germY}$, $\theta$ fixes the classes of constants, $\theta(\mathrm{mkS}\,X_k) \equiv \mathrm{mkS}\big(\sum_i M_{ik}X_i\big)$ modulo the square of the ideal generated by the classes of $X_0,X_1$, $c^{q+1} \equiv 1$ and $M_{ik} \equiv c\,\gamma_{ik}$ modulo $\mathfrak m_{W_1}$, moreover $c \equiv 1 \pmod{\mathfrak m_{W_1}}$ whenever $\gamma_{11} \equiv 1 \pmod{\ell}$, and $c \not\equiv 1 \pmod{\mathfrak m_{W_1}}$ whenever $\gamma \in \Gamma(q)$ and $\tau$ is not the identity; (v) for all integers $a_1,b_1,a_2,b_2$ and all prime ideals $P_1,P_2$ of $S$, each not containing both classes $\mathrm{mkS}\,X_0$, $\mathrm{mkS}\,X_1$, each containing the class of the constant $\sigma_1\varpi$, and each containing an element $\mathrm{mkS}(a_iX_0+b_iX_1+h_i)$ with $h_i \in (X_0,X_1)^2$, if $q \nmid a_1b_2-a_2b_1$ then the contractions of $P_1$ and $P_2$ to $\mathcal{O}_{X,z}$ along $e_1 \circ \mathrm{toC}$ are distinct; (vi) for a prime ideal $P$ of $S$ not containing both classes of $X_0,X_1$, containing the class of $\sigma_1\varpi$ and containing some $\mathrm{mkS}(X_0+h)$ with $h \in (X_0,X_1)^2$, and for $a \in C$, the image $\mathrm{toC}(\mathrm{germY}\,a)$ lies in the contraction of $P$ along $e_1$ if and only if every Laurent coefficient of $a$, viewed in $L((\mathsf q))$, lies in the image of $\mathfrak m_A$; (vii) the series [`ModularCurve.jqNModC L q`](def/ModularCurve_JqCoeff.html#L18), obtained from the $j$-expansion by substituting $\mathsf q \mapsto \mathsf q^{q}$, lies in $K$ and in fact in $C$, and there are $a_0 \in A$ with the difference of that element and $a_0$ in $y'$, an integer $e_0 \ge 1$ and $h \in (X_0,X_1)^{e_0}$ such that for all $a,b \in W_1$ not both in $\mathfrak m_{W_1}$ with $a^qb-ab^q \in \mathfrak m_{W_1}$ the element $\sum_{i=0}^{e_0}\mathrm{coeff}_{(i,\,e_0-i)}(h)\,a^{i}b^{\,e_0-i}$ is a unit of $W_1$, and $e_1$ of the image of that difference under $\mathrm{toC}\circ\mathrm{germY}$ equals $\mathrm{mkS}(h)$.
--
--   Centre and blow-up chart. Let $J$ be the ideal of $C$ defined (`hJ`) as the infimum of the set of ideals $J'$ of $C$ for which there are $\gamma \in \Gamma(q) \cap \Gamma_0(M')$ and a level automorphism $\tau$ at $\gamma^{-1}$ preserving $C$ with $J'$ equal to the pullback along $\tau|_C$ of the contraction along $e_1 \circ \mathrm{toC} \circ \mathrm{germY}$ of the ideal of $S$ generated by the classes of $\sigma_1\varpi_t$, $X_0$ and $X_1$. Let $B$ be the $A$-subalgebra of $K$ obtained by restriction of scalars from the $C$-subalgebra generated by $\{x \in K : \exists\, i \in J,\ x\,\varpi_t = i\}$, that is $B = C[J/\varpi_t]$.
--
--   Conclusion. Then: (1) $B$ is a finitely presented $A$-algebra; (2) the quotient $B/\varpi B$ satisfies $\mathrm{Ring.KrullDimLE}\;1$, i.e. has Krull dimension at most one; and (3) there exist a valuation subring $W$ of $K$ and an inclusion $B \subseteq W$ such that: (a) for $x \in L$, the image of $x$ in $K$ lies in $W$ if and only if $x$ comes from $A$, so that $W \cap L = A$; (b) $\mathfrak m_W$ is generated by the image of $\varpi$; (c) $W$ is a discrete valuation ring; (d) for $b \in C$, one has $b \in y$ if and only if the image of $b$ in $K$ lies in $W$ and belongs to $\mathfrak m_W$, so that $\mathfrak m_W \cap C = y$; and (e) for $f \in K$, one has $f \in W$ if and only if there are $g,h \in B$ with $h$, viewed in $W$, outside $\mathfrak m_W$ and $f\,h = g$ in $K$, so that $W$ is the localisation of $B$ at $\mathfrak m_W \cap B$.
--
--   This is the weighted blow-up step in the construction of a regular integral model of the modular curve attached to $\Gamma_{H_1}(q^2M')$ at a supersingular point in characteristic $q$, in the auxiliary $\Gamma_1(\ell)$-type level frame for general $q$: the chart algebra $C$ of elements integral over $A[j]$ is blown up along the orbit centre $J$ with respect to the weight $\varpi_t$, and the resulting chart is shown to be finitely presented with special fibre of dimension at most one, together with the exceptional discrete valuation $W$ cutting out $y$. It feeds [`ModularCurve.FullLevel.AuxLevelOne.exists_blowupChart_eq_adjoin_exceptionalValuation_of_drinfeldChartWitness_of_stalk_drinfeldChart_moduliHasse_of_dvd`](thm.html#ModularCurve.FullLevel.AuxLevelOne.exists_blowupChart_eq_adjoin_exceptionalValuation_of_drinfeldChartWitness_of_stalk_drinfeldChart_moduliHasse_of_dvd), and uses the local Drinfeld-chart presentation $\sigma_1(\varpi_t^{q+1})v_1 = f_1u_1$ of the completed stalk.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevelOne_finitePresentation_krullDimLE_exists_exceptionalValuation_blowupChart_of_drinfeldChartWitness_of_dvd.lean

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

theorem ModularCurve.FullLevel.AuxLevelOne.finitePresentation_krullDimLE_exists_exceptionalValuation_blowupChart_of_drinfeldChartWitness_of_dvd
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

        Algebra.FinitePresentation A ↥B ∧
        Ring.KrullDimLE 1 (↥B ⧸ Ideal.span {algebraMap A ↥B ϖ}) ∧

        ∃ (W : ValuationSubring ↥K) (hBW : ∀ f : ↥K, f ∈ B → f ∈ W),
          (∀ x : L, algebraMap L ↥K x ∈ W ↔ ∃ a : A, algebraMap A L a = x) ∧
          maximalIdeal ↥W = Ideal.span {(⟨algebraMap A ↥K ϖ, hBW _ (B.algebraMap_mem ϖ)⟩ : ↥W)} ∧
          IsDiscreteValuationRing ↥W ∧
          (∀ b : ↥(chartAlgFin A (↥K) j), b ∈ y ↔
            ∃ hb : (b : ↥K) ∈ W, (⟨(b : ↥K), hb⟩ : ↥W) ∈ maximalIdeal ↥W) ∧
          (∀ f : ↥K, f ∈ W ↔ ∃ g h : ↥B, (⟨(h : ↥K), hBW _ h.2⟩ : ↥W) ∉ maximalIdeal ↥W ∧ f * (h : ↥K) = (g : ↥K)) := by sorry
