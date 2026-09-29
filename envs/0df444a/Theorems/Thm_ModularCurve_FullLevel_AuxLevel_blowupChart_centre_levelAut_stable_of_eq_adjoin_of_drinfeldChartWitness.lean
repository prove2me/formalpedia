-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevel_blowupChart_centre_levelAut_stable_of_eq_adjoin_of_drinfeldChartWitness
-- name    : ModularCurve.FullLevel.AuxLevel.blowupChart_centre_levelAut_stable_of_eq_adjoin_of_drinfeldChartWitness
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:14.444979+00:00
-- url     : https://prove2.me/theorems/6d475259-79d0-5986-a591-31090bd5264e
-- title:
--   Level automorphisms stabilise the blow-up centre and chart algebra
-- statement:
--   Arithmetic data. Let $q$ be a prime with $q \ge 5$, let $M'$ be a non-zero natural number with $q \nmid M'$, and let $\ell$ be a prime with $\ell \ge 3$, $\ell \ne q$ and $\ell \nmid M'$. Let $L$ be a field of characteristic zero, $\xi \in L$ a primitive $(q\ell)$-th root of unity, and assume (`hι`) that there is a ring homomorphism $\iota : L \to \mathbb{C}$ with $\iota(\xi) = e^{2\pi i/(q\ell)}$.
--
--   Function field. Let $K$ be an intermediate field of $L \subseteq L((t))$ (Laurent series over $L$) and assume (`hK`) that $K =$ [`ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField ((q*ℓ)^2*M') (ModularCurve.FullLevel.levelH (q*ℓ) M'))`](def/ModularCurve_LaurentCoeff.html#L103), i.e. $K$ is generated over $L$ by the coefficientwise image in $L((t))$ of the $q$-expansion function field of $X_H$ at level $N_0 = (q\ell)^2M'$, where $H =$ `levelH (q*ℓ) M'` is the kernel of the reduction $(\mathbb{Z}/N_0)^\times \to (\mathbb{Z}/q\ell)^\times$, that is, the units congruent to $1$ modulo $q\ell$.
--
--   Coefficient ring. Let $A$ be a Henselian discrete valuation domain with algebraically closed residue field, an $L$-algebra with $L$ as its fraction field, such that $q \in \mathfrak{m}_A$ (`hAq`) and $\xi$ lies in the image of $A \to L$ (`hξA`); $K$ is an $A$-algebra compatibly with $A \to L \to K$. Let $j \in K$, $j \ne 0$, whose Laurent series is [`ModularCurve.coeffEmb L ModularCurve.jq`](def/ModularCurve_LaurentCoeff.html#L81), the image in $L((t))$ of the $q$-expansion $t^{-1} + \dots$ of the modular invariant (`hj`). Let $\varpi$ generate $\mathfrak{m}_A$ (`hϖ`), and let $\varpi_t \in A$ satisfy $\varpi_t^{\,q^2-1} = q u$ for some unit $u$ of $A$ (`hϖt`).
--
--   Chart algebra and supersingular point. Write $C =$ `chartAlgFin A K j` for the $A$-subalgebra of $K$ of elements integral over $A[j]$, and `jChartFin A K j` for $j$ viewed in $C$. Let $y \subseteq C$ be a maximal ideal (`hy`) containing the image of $\varpi$ (`hϖy`) and supersingular in the sense (`hss`) that for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi : C \to \Omega$ with kernel $y$, the value $\varphi(j)$ lies in [`ModularCurve.ssJSet q Ω`](def/ModularCurve_SupersingularModuli.html#L7), the set of elements $j_0 \in \Omega$ such that every elliptic curve over $\Omega$ with invariant $j_0$ has no non-zero point killed by $q$.
--
--   Integral model. Let $\mathfrak{X} =$ [`AlgebraicCurve.TwoChartIntegralModel A K j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236), the pushout of the two chart schemes $\mathrm{Spec}\,C$ and $\mathrm{Spec}\,$`chartAlgInf A K j` along the middle chart, with its structure morphism `toBase` to $\mathrm{Spec}\,A$. Let $z$ be a point of $\mathfrak{X}$, let $\varpi_z$ be the germ at $z$ of the global section of $\mathfrak{X}$ obtained from $\varpi$ along `toBase` (`hϖz`), and assume $\varpi_z \in \mathfrak{m}_{\mathcal{O}_{\mathfrak{X},z}}$ (`hz`). Let $y'$ be a point of $\mathrm{Spec}\,C$ mapping to $z$ under the chart morphism `ιFin` (`hy'`), subject to the same supersingularity condition at `y'.asIdeal` (`hss'`), and with `y'.asIdeal` $= y$ (`hy'y`).
--
--   Drinfeld chart witness. Let $W_1$ be a discrete valuation domain, complete for the adic topology of its maximal ideal, let $\sigma_1 : A \to W_1$ be a ring homomorphism with $\mathfrak{m}_{W_1} = (\sigma_1\varpi)$ (`hσ₁`), and let $f_1, u_1, v_1 \in W_1[[X_0,X_1]]$ with $u_1, v_1$ units and $f_1 - (X_0X_1^q - X_0^qX_1) \in (X_0,X_1)^{q+2}$ (`hf₁`, where $X_0X_1^q - X_0^qX_1$ is [`DrinfeldCurve.LocalChart.drinfeldForm q W₁`](def/DrinfeldCurve_LocalChart.html#L18)). Put
--   $$S = W_1[[X_0,X_1]]\big/\big(C(\sigma_1(\varpi_t^{\,q+1}))\,v_1 - f_1u_1\big),$$
--   with quotient map $\mathrm{mk}_S$, and let $e_1$ be a ring isomorphism from the $\mathfrak{m}$-adic completion $\widehat{\mathcal{O}}_{\mathfrak{X},z}$ of the stalk at $z$ onto $S$. Write $\mathrm{toC}$ for the completion map $\mathcal{O}_{\mathfrak{X},z} \to \widehat{\mathcal{O}}_{\mathfrak{X},z}$, $\mathrm{germY} : C \to \mathcal{O}_{\mathfrak{X},z}$ for the germ map at $z$ through the chart `ιFin`, and $\Psi = e_1 \circ \mathrm{toC} \circ \mathrm{germY} : C \to S$.
--
--   Throughout, a level automorphism attached to $\gamma \in SL_2(\mathbb{Z})$ means an $L$-algebra automorphism $\tau$ of $K$ satisfying [`ModularCurve.FullLevel.IsLevelAutAt L (q*ℓ) ξ (q*ℓ) ((q*ℓ)^2*M') (levelH (q*ℓ) M') γ K τ`](def/ModularCurve_FullLevelLevelAutAt.html#L29): for every weight $k$, every pair $f,g$ of modular forms of weight $k$ for the congruence subgroup $\Gamma_H(N_0)$ attached to $H$, every pair of integral power series $p_f, p_g$ realising their $q$-expansions with $p_g \ne 0$ over $\mathbb{Q}$, every $x \in K$ whose Laurent series is the image of $p_f/p_g$ under `coeffEmb L`, and every $\iota : L \to \mathbb{C}$ with $\iota(\xi) = e^{2\pi i/(q\ell)}$, the coefficientwise image of $\tau x$ under $\iota$ times the $q$-expansion of $g|_k\,$`conjElemN (q*ℓ) γ` equals the $q$-expansion of $f|_k\,$`conjElemN (q*ℓ) γ`, where `conjElemN m γ` is the matrix $\begin{pmatrix} a & b/m \\ mc & d\end{pmatrix}$ for $\gamma = \begin{pmatrix} a & b \\ c & d\end{pmatrix}$. In the hypotheses and in the conclusion the relevant automorphisms are those attached to $\gamma^{-1}$.
--
--   The hypothesis `hW₁` (seven conjuncts) requires: (1) for every $a \in A$, $\Psi$-compatibility of constants, namely $e_1$ of the image of $a$ in $\widehat{\mathcal{O}}_{\mathfrak{X},z}$ is $\mathrm{mk}_S(C(\sigma_1 a))$; (2) for every $\gamma \in \Gamma_0(M')$ and every level automorphism $\tau$ attached to $\gamma^{-1}$, $\tau$ maps $C$ into $C$; (3) for every $\gamma \in \Gamma_0(M') \cap \Gamma(\ell)$, every $\tau$ attached to $\gamma^{-1}$ preserving $C$, and every $a \in C$, one has $\tau a - a \in y'$; (4) for every $\gamma \in \Gamma_0(M')$, every $\tau$ attached to $\gamma^{-1}$ preserving $C$ and satisfying $\tau a - a \in y'$ for all $a \in C$, there exist a ring automorphism $\theta$ of $S$, an element $c \in W_1$ and a matrix $M \in M_2(W_1)$ such that $\theta \circ \Psi = \Psi \circ \tau|_C$, $\theta$ fixes all constants $\mathrm{mk}_S(C(w))$, $\theta(\mathrm{mk}_S X_{j_0}) \equiv \mathrm{mk}_S\big(\sum_{i_0} C(M_{i_0 j_0})X_{i_0}\big)$ modulo $(\mathrm{mk}_S X_0, \mathrm{mk}_S X_1)^2$, $c^{q+1} \equiv 1$ and $M_{i_0 j_0} \equiv c\,\gamma_{i_0 j_0}$ modulo $\mathfrak{m}_{W_1}$, $c \equiv 1$ modulo $\mathfrak{m}_{W_1}$ when $\gamma \in \Gamma(\ell)$, and $c \not\equiv 1$ modulo $\mathfrak{m}_{W_1}$ when $\gamma \in \Gamma(q)$ and $\tau \ne \mathrm{id}$; (5) for integers $a_1,b_1,a_2,b_2$ and primes $P_1,P_2$ of $S$, each omitting at least one of $\mathrm{mk}_S X_0, \mathrm{mk}_S X_1$, each containing $\mathrm{mk}_S(C(\sigma_1\varpi))$, each containing some $\mathrm{mk}_S(C(a_i)X_0 + C(b_i)X_1 + h)$ with $h \in (X_0,X_1)^2$, and with $q \nmid a_1b_2 - a_2b_1$, the contractions of $P_1$ and $P_2$ to the stalk along $e_1 \circ \mathrm{toC}$ are distinct; (6) for a prime $P$ of $S$ omitting one of $\mathrm{mk}_S X_0, \mathrm{mk}_S X_1$, containing $\mathrm{mk}_S(C(\sigma_1\varpi))$ and containing some $\mathrm{mk}_S(C(1)X_0 + C(0)X_1 + h)$ with $h \in (X_0,X_1)^2$, and for $a \in C$: $\mathrm{toC}(\mathrm{germY}(a))$ lies in the contraction of $P$ along $e_1$ if and only if every Laurent coefficient of $a$ in $L((t))$ lies in the image of $\mathfrak{m}_A$; (7) a witness clause for the series [`ModularCurve.jqNModC L (q*ℓ)`](def/ModularCurve_JqCoeff.html#L18) (the $j$-expansion with $t$ replaced by $t^{q\ell}$): it lies in $K$ and in $C$, there is $a_0 \in A$ with the difference of the corresponding element of $C$ and $a_0$ in $y'$, and there are $e_0 \ge 1$ and $h \in (X_0,X_1)^{e_0}$ such that for all $a,b \in W_1$, at least one a unit, with $a^qb - ab^q \in \mathfrak{m}_{W_1}$, the element $\sum_{i=0}^{e_0}\mathrm{coeff}_{(i,\,e_0-i)}(h)\,a^ib^{\,e_0-i}$ is a unit of $W_1$, and $\Psi$ of that difference equals $\mathrm{mk}_S(h)$.
--
--   Centre and blow-up algebra. Let $J$ be an ideal of $C$ and assume (`hJ`) that $J$ is the infimum of the set of ideals $J'$ of $C$ of the form
--   $$J' = (\tau|_C)^{-1}\Big(\Psi^{-1}\big(\mathrm{mk}_S(C(\sigma_1\varpi_t)), \mathrm{mk}_S X_0, \mathrm{mk}_S X_1\big)\Big),$$
--   as $\gamma$ ranges over $\Gamma(q) \cap \Gamma_0(M')$ and $\tau$ over level automorphisms attached to $\gamma^{-1}$ preserving $C$. Let $B$ be the $A$-subalgebra of $K$ given (`hB`) by restriction of scalars of the $C$-subalgebra generated by $\{x \in K : \exists\, i \in J,\ x\cdot\varpi_t = i\}$, that is, $B = C[J/\varpi_t]$.
--
--   Conclusion. Three assertions hold.
--
--   (i) For every $\gamma \in \Gamma_0(M')$, every level automorphism $\tau$ attached to $\gamma^{-1}$ preserving $C$, such that $\tau a - a \in y$ for all $a \in C$, and every $a \in C$:
--   $$\Psi(a) \in \big(\mathrm{mk}_S(C(\sigma_1\varpi_t)), \mathrm{mk}_S X_0, \mathrm{mk}_S X_1\big) \iff \Psi(\tau a) \in \big(\mathrm{mk}_S(C(\sigma_1\varpi_t)), \mathrm{mk}_S X_0, \mathrm{mk}_S X_1\big).$$
--
--   (ii) For every $\gamma \in \Gamma_0(M')$, every level automorphism $\tau$ attached to $\gamma^{-1}$, every $a \in C$ and every proof that $\tau a \in C$: $a \in J$ if and only if $\tau a$, viewed in $C$, lies in $J$.
--
--   (iii) For every $\gamma \in \Gamma_0(M')$ and every level automorphism $\tau$ attached to $\gamma^{-1}$: $\tau$ maps $B$ into $B$, i.e. $f \in B$ implies $\tau f \in B$.
--
--   This is the equivariance statement for the weighted blow-up of the two-chart integral model at a supersingular point with a Drinfeld local chart: the centre $J$, defined as the intersection of the pullbacks of the ideal $(\sigma_1\varpi_t, X_0, X_1)$ over the level automorphisms coming from $\Gamma(q) \cap \Gamma_0(M')$, is stable under all level automorphisms attached to $\Gamma_0(M')$, and so therefore is the blown-up chart algebra $B = C[J/\varpi_t]$. It feeds the downstream analysis of the Drinfeld fibre, its decomposition and inertia, and of the primes of the blow-up lying over supersingular points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevel_blowupChart_centre_levelAut_stable_of_eq_adjoin_of_drinfeldChartWitness.lean

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

theorem ModularCurve.FullLevel.AuxLevel.blowupChart_centre_levelAut_stable_of_eq_adjoin_of_drinfeldChartWitness
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

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            ∀ hpres : (∀ a : ↥K, a ∈ chartAlgFin A (↥K) j → τ a ∈ chartAlgFin A (↥K) j),
              (∀ a : ↥(chartAlgFin A (↥K) j),
                (((τ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpres) a : ↥(chartAlgFin A (↥K) j)) - a ∈ y) →
              ∀ a : ↥(chartAlgFin A (↥K) j),
                (e₁ : CMP →+* S) (toC (germY a)) ∈ Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖt)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)} ↔
                (e₁ : CMP →+* S) (toC (germY (((τ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpres) a))) ∈ Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖt)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            ∀ (a : ↥(chartAlgFin A (↥K) j)) (ha : τ (a : ↥K) ∈ chartAlgFin A (↥K) j),
              a ∈ J ↔ (⟨τ (a : ↥K), ha⟩ : ↥(chartAlgFin A (↥K) j)) ∈ J) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            ∀ f : ↥K, f ∈ B → τ f ∈ B) := by sorry
