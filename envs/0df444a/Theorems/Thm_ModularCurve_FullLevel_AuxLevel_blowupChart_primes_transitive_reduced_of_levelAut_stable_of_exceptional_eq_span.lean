-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevel_blowupChart_primes_transitive_reduced_of_levelAut_stable_of_exceptional_eq_span
-- name    : ModularCurve.FullLevel.AuxLevel.blowupChart_primes_transitive_reduced_of_levelAut_stable_of_exceptional_eq_span
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:14.444979+00:00
-- url     : https://prove2.me/theorems/ac3a367b-cc55-5202-aab0-bbe2ddcefe92
-- title:
--   Transitivity and reducedness for the blow-up chart above varpi
-- statement:
--   Numerical and field data. Let $q$ be a prime with $q\ge 5$, let $M'$ be a non-zero natural number with $q\nmid M'$, let $\ell$ be a prime with $\ell\ge 3$, $\ell\ne q$ and $\ell\nmid M'$. Let $L$ be a field of characteristic zero and $\xi\in L$ a primitive $(q\ell)$-th root of unity; the hypothesis `hι` requires a ring homomorphism $\iota:L\to\mathbb C$ with $\iota\xi=\exp(2\pi i/(q\ell))$. Let $K$ be an intermediate field of $L\subset L((t))$ with $K=$ [`ModularCurve.laurentBaseChange L`](def/ModularCurve_LaurentCoeff.html#L103) applied to [`ModularCurve.xHFunctionField ((q*ℓ)^2*M') (ModularCurve.FullLevel.levelH (q*ℓ) M')`](def/ModularCurve_XH.html#L79), that is, $K$ is generated over $L$ inside $L((t))$ by the coefficientwise images of the $\mathbb Q$-rational $q$-expansion function field of level $N_0=(q\ell)^2M'$ with character subgroup `levelH (q*ℓ) M'`, the kernel of the reduction $(\mathbb Z/N_0)^\times\to(\mathbb Z/q\ell)^\times$, i.e. the units congruent to $1$ modulo $q\ell$.
--
--   Base ring and $j$. Let $A$ be a discrete valuation ring which is a Henselian local domain with algebraically closed residue field, with $L$ as an $A$-algebra and as its fraction field, and with a compatible $A$-algebra structure on $K$; assume $q\in\mathfrak m_A$ (`hAq`) and that $\xi$ lies in the image of $A\to L$ (`hξA`). Let $\varpi$ generate $\mathfrak m_A$ (`hϖ`) and let $\varpi_t\in A$ satisfy $\varpi_t^{\,q^2-1}=qu$ for some unit $u$ (`hϖt`). Let $j\in K$, $j\ne 0$, whose Laurent expansion is the image under [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81) of the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) of the modular $j$-function (`hj`). Here `chartAlgFin A ↥K j` is the $A$-subalgebra of $K$ of elements integral over $A[j]$, and `jChartFin A ↥K j` is $j$ regarded in it.
--
--   The supersingular point. Let $y$ be a maximal ideal of `chartAlgFin A ↥K j` containing the image of $\varpi$ (`hy`, `hϖy`), and assume (`hss`) that for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi$ from the chart algebra to $\Omega$ with kernel $y$, the value $\varphi(j)$ lies in [`ModularCurve.ssJSet q Ω`](def/ModularCurve_SupersingularModuli.html#L7), i.e. every elliptic Weierstrass curve over $\Omega$ with that $j$-invariant has trivial $q$-torsion.
--
--   The point of the integral model. Let $z$ be a point of the two-chart integral model $X=$ [`AlgebraicCurve.TwoChartIntegralModel A ↥K j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) (the pushout of the two affine charts), let $\varpi_z$ be the germ at $z$ of the global section of $X$ obtained from $\varpi$ along the structure morphism $X\to\operatorname{Spec}A$ (`hϖz`), and assume $\varpi_z$ lies in the maximal ideal of the stalk $\mathcal O_{X,z}$ (`hz`). Let $y'$ be a point of $\operatorname{Spec}$ of the chart algebra mapping to $z$ under the chart morphism `ιFin` (`hy'`), subject to the same supersingularity condition for $y'$ (`hss'`), and with $y'.\mathrm{asIdeal}=y$ (`hy'y`).
--
--   The Drinfeld local chart. Let $W_1$ be a complete discrete valuation ring (a domain, adically complete for its maximal ideal) with a ring homomorphism $\sigma_1:A\to W_1$ such that $\mathfrak m_{W_1}=(\sigma_1\varpi)$ (`hσ₁`), and let $f_1,u_1,v_1\in W_1[[X_0,X_1]]$ with $u_1,v_1$ units and $f_1-(X_0X_1^q-X_0^qX_1)\in(X_0,X_1)^{q+2}$ (`hf₁`), where $X_0X_1^q-X_0^qX_1$ is [`DrinfeldCurve.LocalChart.drinfeldForm q W₁`](def/DrinfeldCurve_LocalChart.html#L18). Let $e_1$ be a ring isomorphism from the adic completion of $\mathcal O_{X,z}$ onto
--   $$S=W_1[[X_0,X_1]]\big/\big(C(\sigma_1(\varpi_t^{\,q+1}))v_1-f_1u_1\big).$$
--   Write $\mathrm{toC}$ for the map from $\mathcal O_{X,z}$ to its completion, $\mathrm{mkS}$ for the quotient map onto $S$, and `germY` for the canonical homomorphism from the chart algebra to $\mathcal O_{X,z}$ determined by the chart `ιFin` and the point $y'$ over $z$. Throughout, an automorphism $\tau$ of $K$ over $L$ is called a level automorphism at $\gamma^{-1}$ when [`ModularCurve.FullLevel.IsLevelAutAt L (q*ℓ) ξ (q*ℓ) ((q*ℓ)^2*M') (ModularCurve.FullLevel.levelH (q*ℓ) M') γ⁻¹ K τ`](def/ModularCurve_FullLevelLevelAutAt.html#L29) holds: for all weights $k$, all modular forms $f,g$ of weight $k$ for the level subgroup attached to $N_0$ and `levelH (q*ℓ) M'` with integral $q$-expansions and $g$ non-zero, and all $x\in K$ whose Laurent series is the quotient of those $q$-expansions, the $\iota$-image of the Laurent series of $\tau x$ times the $q$-expansion of $g\mid_k$ `conjElemN (q*ℓ) γ⁻¹` equals that of $f\mid_k$ `conjElemN (q*ℓ) γ⁻¹`, for any $\iota$ as in `hι`.
--
--   The hypothesis `hW₁` (seven clauses) requires: (1) for every $a\in A$, $e_1$ carries the image in the completion of the germ at $z$ of the section coming from $a$ to $\mathrm{mkS}(C(\sigma_1a))$; (2) every level automorphism $\tau$ at $\gamma^{-1}$ with $\gamma\in\Gamma_0(M')$ maps the chart algebra into itself; (3) for $\gamma\in\Gamma_0(M')\cap\Gamma(\ell)$ and $\tau$ a level automorphism at $\gamma^{-1}$ preserving the chart algebra, $\tau a-a\in y'.\mathrm{asIdeal}$ for every $a$ in the chart algebra; (4) for $\gamma\in\Gamma_0(M')$ and $\tau$ a level automorphism at $\gamma^{-1}$ preserving the chart algebra and acting trivially modulo $y'.\mathrm{asIdeal}$, there exist a ring automorphism $\theta$ of $S$, an element $c\in W_1$ and a matrix $M\in\mathrm{Mat}_2(W_1)$ such that $\theta$ intertwines $e_1\circ\mathrm{toC}\circ$`germY` with the restriction of $\tau$, $\theta$ fixes the images of the constants $C(w)$, $\theta(\mathrm{mkS}\,X_j)-\mathrm{mkS}\big(\sum_iC(M_{ij})X_i\big)$ lies in the square of the ideal generated by the images of $X_0,X_1$, $c^{q+1}\equiv1$ and $M_{ij}\equiv c\,\gamma_{ij}$ modulo $\mathfrak m_{W_1}$, $c\equiv1$ modulo $\mathfrak m_{W_1}$ if $\gamma\in\Gamma(\ell)$, and $c\not\equiv1$ modulo $\mathfrak m_{W_1}$ if $\gamma\in\Gamma(q)$ and $\tau$ is not the identity; (5) for integers $a_1,b_1,a_2,b_2$ and prime ideals $P_1,P_2$ of $S$, each omitting at least one of the images of $X_0,X_1$, each containing $\mathrm{mkS}(C(\sigma_1\varpi))$, and each containing an element $\mathrm{mkS}(C(a_i)X_0+C(b_i)X_1+h)$ with $h\in(X_0,X_1)^2$, if $q\nmid a_1b_2-a_2b_1$ then the contractions of $P_1$ and $P_2$ to $\mathcal O_{X,z}$ along $e_1\circ\mathrm{toC}$ are distinct; (6) for a prime $P$ of $S$ omitting at least one of the images of $X_0,X_1$, containing $\mathrm{mkS}(C(\sigma_1\varpi))$ and containing $\mathrm{mkS}(C(1)X_0+C(0)X_1+h)$ for some $h\in(X_0,X_1)^2$, an element $a$ of the chart algebra satisfies $\mathrm{toC}(\mathrm{germY}\,a)\in e_1^{-1}P$ if and only if every Laurent coefficient of $a$ lies in the image of $\mathfrak m_A$ under $A\to L$; (7) the element [`ModularCurve.jqNModC L (q*ℓ)`](def/ModularCurve_JqCoeff.html#L18) lies in $K$ and in the chart algebra, and there are $a_0\in A$ with the difference of that element and $a_0$ in $y'.\mathrm{asIdeal}$, an integer $e_0\ge1$ and $h\in(X_0,X_1)^{e_0}$ such that for all $a,b\in W_1$, at least one of them a unit, with $a^qb-ab^q\in\mathfrak m_{W_1}$, the sum $\sum_{i=0}^{e_0}\big(\text{coefficient of }X_0^iX_1^{e_0-i}\text{ in }h\big)a^ib^{e_0-i}$ is a unit, and $e_1(\mathrm{toC}(\mathrm{germY}(\ldots-a_0)))=\mathrm{mkS}\,h$.
--
--   The blow-up chart. Let $J$ be the ideal of the chart algebra given (`hJ`) as the infimum of all ideals of the form $\tau^{-1}$ of the contraction along $e_1\circ\mathrm{toC}\circ$`germY` of the ideal of $S$ generated by $\mathrm{mkS}(C(\sigma_1\varpi_t))$, $\mathrm{mkS}\,X_0$ and $\mathrm{mkS}\,X_1$, as $\gamma$ ranges over $\Gamma(q)\cap\Gamma_0(M')$ and $\tau$ over the level automorphisms at $\gamma^{-1}$ preserving the chart algebra. Let $B$ be the $A$-subalgebra of $K$ obtained by adjoining to the chart algebra all $x\in K$ with $x\varpi_t\in J$ (`hB`), and let $W$ be a valuation subring of $K$ containing $B$ (`hBW`). The hypothesis `hR1` states that the chart algebra is contained in $B$ and that every element of $K$ is a quotient $g/h$ with $g,h\in B$, $h\ne0$. The hypothesis `hR2` states that $A\to B$ is formally smooth and of finite presentation and that $B/\varpi B$ has Krull dimension at most $1$. The hypothesis `hR3` (five clauses) states that an element of $L$ lies in $W$ exactly when it comes from $A$; that $\mathfrak m_W$ is generated by the image of $\varpi$; that $W$ is a discrete valuation ring; that an element $b$ of the chart algebra lies in $y$ exactly when it lies in $W$ and in $\mathfrak m_W$; and that $f\in K$ lies in $W$ exactly when $f=g/h$ with $g,h\in B$ and $h\notin\mathfrak m_W$.
--
--   Stability and remaining hypotheses. `hJstab`: for $\gamma\in\Gamma_0(M')$ and $\tau$ a level automorphism at $\gamma^{-1}$, an element $a$ of the chart algebra with $\tau a$ again in the chart algebra lies in $J$ if and only if $\tau a$ does. `hBstab`: such $\tau$ map $B$ into $B$. `hPid`: an element $b\in B$ lies in $\mathfrak m_W$ if and only if it lies in the ideal of $B$ generated by the image of $y$. `hJy`: $J\subseteq y$. `hϖtJ`: the image of $\varpi_t$ in the chart algebra lies in $J$.
--
--   Conclusion. Two statements hold. First: for every prime ideal $Q$ of $B$ containing the image of $\varpi$ there exist $\gamma\in SL_2(\mathbb Z)$ with $\gamma\in\Gamma(q)$ and $\gamma\in\Gamma_0(M')$, and an $L$-automorphism $\tau$ of $K$ which is a level automorphism at $\gamma^{-1}$, such that for every $b\in B$ whose image in $W$ lies in $\mathfrak m_W$ one has $\tau b\in B$, and $\tau b$, viewed in $B$, lies in $Q$. Second: if $b\in B$ is such that for all $\gamma\in\Gamma(q)\cap\Gamma_0(M')$ and every level automorphism $\tau$ at $\gamma^{-1}$, whenever $\tau b$ lies in $B$ its image in $W$ lies in $\mathfrak m_W$, then the image of $\varpi$ under $A\to B$ divides $b$.
--
--   The two assertions are the transitivity of the action of the automorphisms attached to $\Gamma(q)\cap\Gamma_0(M')$ on the primes of the blow-up chart $B$ above $\varpi$, together with the divisibility form of reducedness of the special fibre $B/\varpi B$. They are consumed by the statement describing the decomposition of the Drinfeld fibre of the blow-up chart under these level automorphisms, in the analysis of the local structure of the modular curve of level $(q\ell)^2M'$ at a supersingular point in characteristic $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevel_blowupChart_primes_transitive_reduced_of_levelAut_stable_of_exceptional_eq_span.lean

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

theorem ModularCurve.FullLevel.AuxLevel.blowupChart_primes_transitive_reduced_of_levelAut_stable_of_exceptional_eq_span
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
        {x : ↥K | ∃ i ∈ J, x * algebraMap A ↥K ϖt = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}).restrictScalars A)

    (W : ValuationSubring ↥K) (hBW : ∀ f : ↥K, f ∈ B → f ∈ W)
    (hR1 :

      chartAlgFin A (↥K) j ≤ B ∧
      (∀ f : ↥K, ∃ g h : ↥B, (h : ↥K) ≠ 0 ∧ f * (h : ↥K) = (g : ↥K)))
    (hR2 :

      Algebra.FormallySmooth A ↥B ∧ Algebra.FinitePresentation A ↥B ∧
      Ring.KrullDimLE 1 (↥B ⧸ Ideal.span {algebraMap A ↥B ϖ}))
    (hR3 :

      (∀ x : L, algebraMap L ↥K x ∈ W ↔ ∃ a : A, algebraMap A L a = x) ∧
      maximalIdeal ↥W = Ideal.span {(⟨algebraMap A ↥K ϖ, hBW _ (B.algebraMap_mem ϖ)⟩ : ↥W)} ∧
      IsDiscreteValuationRing ↥W ∧
      (∀ b : ↥(chartAlgFin A (↥K) j), b ∈ y ↔
        ∃ hb : (b : ↥K) ∈ W, (⟨(b : ↥K), hb⟩ : ↥W) ∈ maximalIdeal ↥W) ∧
      (∀ f : ↥K, f ∈ W ↔ ∃ g h : ↥B, (⟨(h : ↥K), hBW _ h.2⟩ : ↥W) ∉ maximalIdeal ↥W ∧ f * (h : ↥K) = (g : ↥K)))

    (hJstab : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
      ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
        ∀ (a : ↥(chartAlgFin A (↥K) j)) (ha : τ (a : ↥K) ∈ chartAlgFin A (↥K) j),
          a ∈ J ↔ (⟨τ (a : ↥K), ha⟩ : ↥(chartAlgFin A (↥K) j)) ∈ J)

    (hBstab : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
      ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
        ∀ f : ↥K, f ∈ B → τ f ∈ B)

    (hPid : ∀ b : ↥B, (⟨(b : ↥K), hBW _ b.2⟩ : ↥W) ∈ maximalIdeal ↥W ↔
      b ∈ Ideal.span ((fun c : ↥(chartAlgFin A (↥K) j) => (⟨(c : ↥K), hR1.1 c.2⟩ : ↥B)) '' (y : Set ↥(chartAlgFin A (↥K) j))))

    (hJy : J ≤ y) (hϖtJ : algebraMap A ↥(chartAlgFin A (↥K) j) ϖt ∈ J) :

      (∀ Q : Ideal ↥B, Q.IsPrime → algebraMap A ↥B ϖ ∈ Q →
        ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧
          ∃ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ ∧
            ∀ b : ↥B, (⟨(b : ↥K), hBW _ b.2⟩ : ↥W) ∈ maximalIdeal ↥W → τ (b : ↥K) ∈ B ∧ ∀ hb : τ (b : ↥K) ∈ B, (⟨τ (b : ↥K), hb⟩ : ↥B) ∈ Q) ∧

      (∀ b : ↥B, (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            ∀ hb : τ (b : ↥K) ∈ B, (⟨τ (b : ↥K), hBW _ hb⟩ : ↥W) ∈ maximalIdeal ↥W) →
        algebraMap A ↥B ϖ ∣ b) := by sorry
