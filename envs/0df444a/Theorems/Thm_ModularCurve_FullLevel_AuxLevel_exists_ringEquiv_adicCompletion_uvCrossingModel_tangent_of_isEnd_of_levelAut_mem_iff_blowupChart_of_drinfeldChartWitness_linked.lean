-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_ringEquiv_adicCompletion_uvCrossingModel_tangent_of_isEnd_of_levelAut_mem_iff_blowupChart_of_drinfeldChartWitness_linked
-- name    : ModularCurve.FullLevel.AuxLevel.exists_ringEquiv_adicCompletion_uvCrossingModel_tangent_of_isEnd_of_levelAut_mem_iff_blowupChart_of_drinfeldChartWitness_linked
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:22.181174+00:00
-- url     : https://prove2.me/theorems/d3e9793c-0995-5461-9a14-e780a42eb171
-- title:
--   Crossing presentation at a τ₀-stable end with tangent character
-- statement:
--   **Data.** Fix a prime $q\ge 5$, a nonzero natural number $M'$ with $q\nmid M'$, and a prime $\ell\ge 3$ with $\ell\ne q$ and $\ell\nmid M'$. Let $L$ be a field of characteristic $0$ and $\xi\in L$ a primitive $(q\ell)$-th root of unity; the hypothesis `hι` asks that some ring homomorphism $L\to\mathbb{C}$ send $\xi$ to $\exp(2\pi i/(q\ell))$. Let $K$ be an intermediate field of $L\subseteq\operatorname{LaurentSeries} L$ which, by `hK`, is the field [`ModularCurve.laurentBaseChange`](def/ModularCurve_LaurentCoeff.html#L103) obtained by adjoining to $L$ the coefficientwise images of the $q$-expansion function field [`ModularCurve.xHFunctionField ((q*ℓ)^2*M') (ModularCurve.FullLevel.levelH (q*ℓ) M')`](def/ModularCurve_XH.html#L79); here `levelH (q*ℓ) M'` is the kernel of the reduction $(\mathbb{Z}/(q\ell)^2M')^\times\to(\mathbb{Z}/q\ell)^\times$, that is, the group of units congruent to $1$ modulo $q\ell$.
--
--   Let $A$ be a henselian discrete valuation ring with algebraically closed residue field, equipped with an $A$-algebra structure on $L$ making $L$ its fraction field, with $q\in\mathfrak m_A$ (`hAq`) and with $\xi$ in the image of $A$ (`hξA`), together with a compatible $A$-algebra structure on $K$. Let $j\in K$ be nonzero with Laurent expansion the coefficientwise image of the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) of the modular invariant, let $\varpi$ generate $\mathfrak m_A$ (`hϖ`), and let $\varpi_t\in A$ satisfy $\varpi_t^{\,q^2-1}=q\cdot(\text{unit})$ (`hϖt`). Write $C:=$ `chartAlgFin A K j` for the $A$-subalgebra of elements of $K$ integral over $A[j]$, and $X:=$ [`AlgebraicCurve.TwoChartIntegralModel A K j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) for the scheme obtained as the pushout glueing $\operatorname{Spec} C$ to $\operatorname{Spec}$ of the corresponding algebra for $j^{-1}$, with structure morphism `toBase` to $\operatorname{Spec} A$.
--
--   Let $y$ be a maximal ideal of $C$ containing $\varpi$ (`hy`, `hϖy`) which is supersingular in the sense of `hss`: for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi:C\to\Omega$ with kernel $y$, the element $\varphi(j)$ lies in [`ModularCurve.ssJSet q Ω`](def/ModularCurve_SupersingularModuli.html#L7), the set of those elements of $\Omega$ such that every elliptic curve over $\Omega$ with that $j$-invariant has no nonzero point killed by $q$.
--
--   **The rigidity list.** The hypothesis `hArig` asserts, for every point $z$ of $X$ at which the germ of $\varpi$ lies in the maximal ideal of the stalk and every point $y'$ of $\operatorname{Spec} C$ mapping to $z$ under `ιFin` and supersingular in the above sense, the existence of a complete discrete valuation domain $W$, a ring homomorphism $\sigma:A\to W$ with $\mathfrak m_W=(\sigma\varpi)$, power series $f,u,v\in W[[X_0,X_1]]$ with $u,v$ units and $f\equiv X_0X_1^q-X_0^qX_1$ modulo $(X_0,X_1)^{q+2}$ (the Drinfeld form [`DrinfeldCurve.LocalChart.drinfeldForm`](def/DrinfeldCurve_LocalChart.html#L18)), and a ring isomorphism
--   $$e:\ \widehat{\mathcal O}_{X,z}\ \xrightarrow{\ \sim\ }\ S:=W[[X_0,X_1]]/\bigl(C(\sigma(\varpi_t^{\,q+1}))\,v-f\,u\bigr),$$
--   the completion being the adic completion of the stalk at its maximal ideal, subject to seven clauses. Writing `toC` for the map from the stalk to its completion, `mkS` for the quotient map onto $S$, and `germY` for the homomorphism $C\to\mathcal O_{X,z}$ obtained from the image of $\operatorname{Spec} C$ in $X$, these clauses are: (R1) $e$ carries the image of $a\in A$ to the class of $C(\sigma a)$; (R2) for $\gamma\in\Gamma_0(M')$, every $\tau\in\operatorname{Aut}_L(K)$ with `IsLevelAutAt L (q*ℓ) ξ (q*ℓ) ((q*ℓ)^2*M') (levelH (q*ℓ) M') γ⁻¹ K τ` — that is, $\tau$ realises on $K$ the action of the matrix `conjElemN (q*ℓ) γ⁻¹` on quotients of $q$-expansions of modular forms of level $\Gamma_H$, read through the embedding $L\to\mathbb{C}$ normalised by $\xi$ — maps $C$ into $C$; (R3) for $\gamma\in\Gamma_0(M')\cap\Gamma(\ell)$, such a $\tau$ restricted to $C$ is the identity modulo $y'$; (R4) for $\gamma\in\Gamma_0(M')$ and such a $\tau$ preserving $C$ and acting trivially modulo $y'$, there are a ring automorphism $\theta$ of $S$, an element $c\in W$ and a matrix $M\in M_2(W)$ such that $\theta$ implements $\tau|_C$ through $e\circ$`toC`$\circ$`germY`, fixes the class of every constant, has linear part $\theta(X_{jj})\equiv\sum_{ii}M_{ii,jj}X_{ii}$ modulo the square of the ideal generated by the classes of $X_0,X_1$, and satisfies $c^{q+1}\equiv 1$, $M_{ii,jj}\equiv c\,\gamma_{ii,jj}$ modulo $\mathfrak m_W$, $c\equiv1$ whenever $\gamma\in\Gamma(\ell)$, and $c\not\equiv1$ whenever $\gamma\in\Gamma(q)$ and $\tau\ne\mathrm{id}$; (R5) two primes $P_1,P_2$ of $S$ containing the class of $C(\sigma\varpi)$, each omitting at least one of the classes of $X_0,X_1$, and each containing an element $C(a_i)X_0+C(b_i)X_1+h$ with $h\in(X_0,X_1)^2$, have distinct contractions along $e\circ$`toC` as soon as $q\nmid a_1b_2-a_2b_1$; (R6) for a prime $P$ of $S$ as in (R5) with tangent direction $(1,0)$, an element $a\in C$ lies in the contraction of $P$ along $e$ precisely when every Laurent coefficient of $a$ lies in the image of $\mathfrak m_A$; (R7) the element [`ModularCurve.jqNModC L (q*ℓ)`](def/ModularCurve_JqCoeff.html#L18) lies in $K$ and in $C$, and there are $a_0\in A$ with the corresponding difference in $y'$, an integer $e_0\ge1$ and $h\in(X_0,X_1)^{e_0}$ such that the degree-$e_0$ form $\sum_{i\le e_0}\operatorname{coeff}_{(i,e_0-i)}(h)\,a^ib^{e_0-i}$ is a unit for all $a,b\in W$ with $a$ or $b$ a unit and $a^qb-ab^q\in\mathfrak m_W$, and $e$ sends the image of that difference to the class of $h$.
--
--   **The pinned point and its chart.** There are given a point $z$ of $X$, the germ $\varpi_z$ of $\varpi$ at $z$ lying in the maximal ideal of the stalk (`hϖz`, `hz`), a point $y'$ of $\operatorname{Spec} C$ with `ιFin`-image $z$ (`hy'`), supersingular (`hss'`) and with $y'=y$ (`hy'y`); and there are given a complete discrete valuation domain $W_1$, $\sigma_1:A\to W_1$ with $\mathfrak m_{W_1}=(\sigma_1\varpi)$, series $f_1,u_1,v_1$ with $u_1,v_1$ units and $f_1$ congruent to the Drinfeld form modulo $(X_0,X_1)^{q+2}$, and an isomorphism $e_1$ of the completed stalk with $S:=W_1[[X_0,X_1]]/(C(\sigma_1(\varpi_t^{q+1}))v_1-f_1u_1)$, the hypothesis `hW₁` asserting for this datum exactly the seven clauses (R1)–(R7) above at $z$ and $y'$.
--
--   **Blow-up data.** The ideal $J$ of $C$ is, by `hJ`, the infimum of the ideals $(\tau|_C)^{-1}\bigl((e_1\circ\mathrm{toC}\circ\mathrm{germY})^{-1}(\,(\text{classes of }C(\sigma_1\varpi_t),X_0,X_1)\,)\bigr)$ taken over all $\gamma\in\Gamma(q)\cap\Gamma_0(M')$ and all level automorphisms $\tau$ at $\gamma^{-1}$ preserving $C$. The $A$-subalgebra $B$ of $K$ is, by `hB`, generated over $C$ by $\{x\in K:\ x\varpi_t\in J\}$. A valuation subring $W$ of $K$ is given with $B\subseteq W$ (`hBW`), and:
--
--   `hR1`: $C\subseteq B$ and every element of $K$ is a quotient of elements of $B$. `hR2`: $A\to B$ is formally smooth and of finite presentation, and $B/(\varpi)$ has Krull dimension at most $1$. `hR3` (five clauses): an element of $L$ lands in $W$ exactly when it comes from $A$; $\mathfrak m_W$ is generated by $\varpi$; $W$ is a discrete valuation ring; for $b\in C$, $b\in y$ iff $b\in\mathfrak m_W$; and $W$ is the set of quotients $g/h$ with $g,h\in B$ and $h\notin\mathfrak m_W$. `hEQ` (five clauses): for every $\mathbb{F}_{q^2}$-algebra structure on the residue field $\kappa$ of $A$ there is a surjection $\rho:B\to$ [`DrinfeldCurve.CoordRing q κ`](def/DrinfeldCurve_CoordRing.html#L21) (the quotient of $\kappa[X_0,X_1]$ by `drinfeldPoly q κ`$-1$) with kernel $B\cap\mathfrak m_W$, compatible with $A\to\kappa$, and equivariant in the sense that for $\gamma\in\Gamma_0(M')$ and every level automorphism $\tau$ at $\gamma^{-1}$ preserving $W$ there is a unit $c$ of $\mathbb{F}_{q^2}$ with $(\mathrm{redQ}\,q\,\gamma,c)\in$ [`DrinfeldCurve.hSubgroup q`](def/DrinfeldCurve_CoordRing.html#L276) such that $\rho\circ\tau=$ `hAction` of that pair applied to $\rho$, and $c\ne1$ when $\gamma\in\Gamma(q)$ and $\tau\ne\mathrm{id}$; every level automorphism with $\gamma\in\Gamma_0(M')$ preserves $B$; every prime of $B$ containing $\varpi$ is the locus into which some level automorphism with $\gamma\in\Gamma(q)\cap\Gamma_0(M')$ carries $B\cap\mathfrak m_W$; an element of $B$ carried into $\mathfrak m_W$ by all such automorphisms is divisible by $\varpi$; and a level automorphism with $\gamma\in\Gamma_0(M')$ that preserves $y$ on $C$ preserves $W$.
--
--   **Cyclic and end data.** There are given $n\ge1$ with $n\mid q+1$, an element $\gamma_0\in\Gamma(q)\cap\Gamma_0(M')$, a level automorphism $\tau_0$ at $\gamma_0^{-1}$ preserving $W$ (`hτ₀W`) with $\tau_0^n$ the identity on $B$ (`hcyc1`) and $\tau_0^k$ not the identity on $B$ for $0<k<n$ (`hcyc2`); an integer $m\ge1$ with $\varpi^m=\varpi_t\cdot(\text{unit})$ (`hmt`); and a subring $O$ of $K$ subject to the end condition `hO`: for some nonzero $a\in J$, setting $B_a$ to be the $A$-algebra generated over $C$ by $\{x\in K: xa\in J\}$, there is a maximal ideal $P$ of $B_a$ such that $O$ consists of the quotients $g/h$ with $g,h\in B_a$, $h\notin P$, every element of $y$ lying in $O$ is a non-unit of $O$, and $B$ is not contained in $O$. Finally `hOτ` requires $f\in O\iff\tau_0f\in O$.
--
--   **Conclusion.** Write $\widehat A$ for the adic completion of $A$ at $\mathfrak m_A$ and $\pi$ for the $m$-th power of the image of $\varpi$ in $\widehat A$. Then there exists $\zeta_0\in\widehat A$ with $\zeta_0^{\,n}=1$ and $\zeta_0^{\,k}-1$ a unit for $0<k<n$, such that $O\subseteq W$ and, with $O$ local and noetherian:
--
--   (i) $C\subseteq O$; (ii) an element of $L$ lands in $O$ exactly when it comes from $A$; (iii) for every $f\in O$ there is $a\in A$ whose image lies in $O$ with $f-a$ a non-unit of $O$;
--
--   (iv) and $\varpi$ lies in $O$ and there are $c_x,c_y\in O$, a unit $u$ of $O$, a ring isomorphism
--   $$\iota:\ \widehat O\ \xrightarrow{\ \sim\ }\ \mathrm{UVCrossingModel}\,\widehat A\,\pi\ =\ \widehat A[[X_0,X_1]]/(X_0X_1-C(\pi)),$$
--   $\widehat O$ being the adic completion of $O$ at its maximal ideal, units $\gamma_U,\gamma_V$ of the crossing model, an $\widehat A$-algebra automorphism $\theta_0$ of it, an element $\zeta_0'\in\widehat A$ with $\zeta_0\zeta_0'=1$, and a local ring structure on the crossing model, such that: $c_xc_y=\varpi^m u$ in $O$; $\iota$ sends the image of each $a\in A$ lying in $O$ to the constant `UVCrossingModel.const` of the image of $a$ in $\widehat A$; $\iota(c_x)=\gamma_U\cdot U$ and $\iota(c_y)=\gamma_V\cdot V$ for the two distinguished elements `UVCrossingModel.U`, `UVCrossingModel.V`; $c_y$ lies in $\mathfrak m_W$ and $c_x$ does not, whenever they lie in $W$; $\tau_0$ acts on $\widehat O$ through $\theta_0$, in the sense that $\iota(\tau_0f)=\theta_0(\iota(f))$ for all $f\in O$ with $\tau_0f\in O$; the tangent congruences
--   $$\theta_0(U)-\mathrm{const}(\zeta_0)\,U\ \in\ \mathfrak m^2,\qquad \theta_0(V)-\mathrm{const}(\zeta_0')\,V\ \in\ \mathfrak m^2$$
--   hold in the crossing model; and, finally, the pinning clause: for every $c\in W_1$, every ring automorphism $\theta$ of $S$, every matrix $M_x\in M_2(W_1)$ and every witness that $\tau_0$ preserves $C$, if $\theta$ implements $\tau_0|_C$ through $e_1\circ\mathrm{toC}\circ\mathrm{germY}$, fixes the classes of constants, has linear part $M_x$ modulo the square of the ideal generated by the classes of $X_0,X_1$, and satisfies $M_{x\,ii,jj}\equiv c\,(\gamma_0)_{ii,jj}$ modulo $\mathfrak m_{W_1}$, then for every $a\in A$ with $c-\sigma_1a\in\mathfrak m_{W_1}$ the element $\zeta_0'-a$ of $\widehat A$ is not a unit.
--
--   At a supersingular point of the integral model of the modular curve of level $\Gamma_H$, this statement produces, at one end of the blown-up chart that is stable under the chosen cyclic level automorphism $\tau_0$, a crossing presentation $\widehat O\cong\widehat A[[U,V]]/(UV-\varpi^m)$ on which $\tau_0$ acts diagonally to first order by a root of unity $\zeta_0$ of exact order $n$ and its inverse, the inverse being pinned to the linear scalar read off from the Drinfeld chart. It is the single-end form of the corresponding statement over all ends, which cites it, in the analysis of the reduction of the modular curve used for the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevel_exists_ringEquiv_adicCompletion_uvCrossingModel_tangent_of_isEnd_of_levelAut_mem_iff_blowupChart_of_drinfeldChartWitness_linked.lean

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

theorem ModularCurve.FullLevel.AuxLevel.exists_ringEquiv_adicCompletion_uvCrossingModel_tangent_of_isEnd_of_levelAut_mem_iff_blowupChart_of_drinfeldChartWitness_linked
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

    (hArig : ∀ (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j))
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
            φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω),
      ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
        (_ : IsAdicComplete (IsLocalRing.maximalIdeal W) W) (σ : A →+* W)
        (_ : IsLocalRing.maximalIdeal W = Ideal.span {σ ϖ})
        (f u v : MvPowerSeries (Fin 2) W) (_ : IsUnit u) (_ : IsUnit v)
        (_ : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
          (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (q + 2))
        (e : AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ≃+*
          MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ (ϖt ^ (q + 1))) * v - f * u}),

        let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
        let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        let toC : STK →+* CMP := algebraMap STK CMP
        let S := (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ (ϖt ^ (q + 1))) * v - f * u})
        let mkS : MvPowerSeries (Fin 2) W →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ (ϖt ^ (q + 1))) * v - f * u})
        let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
          ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
              ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y', trivial, hy'⟩).hom.comp
            ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
              (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)

        (∀ a : A, e (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
              (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
            (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
              (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
                ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)))) =
          Ideal.Quotient.mk _ (MvPowerSeries.C (σ a))) ∧

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
                ∃ (θ : S ≃+* S) (c : W) (M : Matrix (Fin 2) (Fin 2) W),

                  (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                    θ (e (toC (germY a))) = e (toC (germY (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a)))) ∧

                  (∀ w : W, θ (mkS (MvPowerSeries.C w)) = mkS (MvPowerSeries.C w)) ∧

                  (∀ jj : Fin 2, θ (mkS (MvPowerSeries.X jj)) -
                      mkS (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) ∈
                    (Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2) ∧
                  (c ^ (q + 1) - 1 ∈ IsLocalRing.maximalIdeal W) ∧
                  (∀ ii jj : Fin 2, M ii jj - c * ((γ ii jj : ℤ) : W) ∈ IsLocalRing.maximalIdeal W) ∧
                  (γ ∈ CongruenceSubgroup.Gamma ℓ → c - 1 ∈ IsLocalRing.maximalIdeal W) ∧

                  (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥K, τ k = k) → c - 1 ∉ IsLocalRing.maximalIdeal W)) ∧

        (∀ (a₁ b₁ a₂ b₂ : ℤ) (P₁ P₂ : Ideal S), P₁.IsPrime → P₂.IsPrime →

          (mkS (MvPowerSeries.X 0) ∉ P₁ ∨ mkS (MvPowerSeries.X 1) ∉ P₁) →
          (mkS (MvPowerSeries.X 0) ∉ P₂ ∨ mkS (MvPowerSeries.X 1) ∉ P₂) →
          mkS (MvPowerSeries.C (σ ϖ)) ∈ P₁ → mkS (MvPowerSeries.C (σ ϖ)) ∈ P₂ →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C ((a₁ : ℤ) : W) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₁ : ℤ) : W) * MvPowerSeries.X 1 + h)
                ∈ P₁) →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C ((a₂ : ℤ) : W) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₂ : ℤ) : W) * MvPowerSeries.X 1 + h)
                ∈ P₂) →
          ¬ ((q : ℤ) ∣ a₁ * b₂ - a₂ * b₁) →
            Ideal.comap ((e : CMP →+* S).comp toC) P₁ ≠ Ideal.comap ((e : CMP →+* S).comp toC) P₂) ∧

        (∀ P : Ideal S, P.IsPrime → (mkS (MvPowerSeries.X 0) ∉ P ∨ mkS (MvPowerSeries.X 1) ∉ P) →
          mkS (MvPowerSeries.C (σ ϖ)) ∈ P →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C (1 : W) * MvPowerSeries.X 0 + MvPowerSeries.C (0 : W) * MvPowerSeries.X 1 + h) ∈ P) →
          ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
            toC (germY a) ∈ Ideal.comap (e : CMP →+* S) P ↔
              ∀ n : ℤ, ∃ m ∈ IsLocalRing.maximalIdeal A,
                (((a : ↥K) : LaurentSeries L).coeff n) = algebraMap A L m) ∧

        (∃ (hjK : ModularCurve.jqNModC L (q * ℓ) ∈ K)
           (hjC : (⟨ModularCurve.jqNModC L (q * ℓ), hjK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
           (a₀ : A) (_ : (⟨(⟨ModularCurve.jqNModC L (q * ℓ), hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) -
              algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a₀ ∈ y'.asIdeal)
           (e₀ : ℕ) (_ : 1 ≤ e₀) (h : MvPowerSeries (Fin 2) W)
           (_ : h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ e₀),
           (∀ a b : W, (a ∉ IsLocalRing.maximalIdeal W ∨ b ∉ IsLocalRing.maximalIdeal W) →
              a ^ q * b - a * b ^ q ∈ IsLocalRing.maximalIdeal W →
              IsUnit (∑ i ∈ Finset.range (e₀ + 1),
                MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (e₀ - i)) h * a ^ i * b ^ (e₀ - i))) ∧
           (e : CMP →+* S) (toC (germY ((⟨(⟨ModularCurve.jqNModC L (q * ℓ), hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) -
              algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a₀))) = mkS h))

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
    (hEQ :

      (∀ (inst : Algebra (GaloisField q 2) (ResidueField A)),
        ∃ (ρ : ↥B →+* DrinfeldCurve.CoordRing q (ResidueField A)),
          Function.Surjective ρ ∧
          (∀ b : ↥B, ρ b = 0 ↔ (⟨(b : ↥K), hBW _ b.2⟩ : ↥W) ∈ maximalIdeal ↥W) ∧
          (∀ a : A, ρ (algebraMap A ↥B a) = algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) (residue A a)) ∧
          (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
            ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
                (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
              (∀ f : ↥K, f ∈ W ↔ τ f ∈ W) →
              ∃ (c : (GaloisField q 2)ˣ) (hmem : (ModularCurve.FullLevel.redQ q γ, c) ∈ DrinfeldCurve.hSubgroup q),
                (∀ (b : ↥B) (hb : τ (b : ↥K) ∈ B), ρ ⟨τ (b : ↥K), hb⟩ = DrinfeldCurve.hAction q (ResidueField A) ⟨_, hmem⟩ (ρ b)) ∧
                (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥K, τ k = k) → c ≠ 1))) ∧

      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
        ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
            (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
          ∀ f : ↥K, f ∈ B → τ f ∈ B) ∧
      (∀ Q : Ideal ↥B, Q.IsPrime → algebraMap A ↥B ϖ ∈ Q →
        ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧
          ∃ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ ∧
            ∀ b : ↥B, (⟨(b : ↥K), hBW _ b.2⟩ : ↥W) ∈ maximalIdeal ↥W → τ (b : ↥K) ∈ B ∧ ∀ hb : τ (b : ↥K) ∈ B, (⟨τ (b : ↥K), hb⟩ : ↥B) ∈ Q) ∧
      (∀ b : ↥B, (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            ∀ hb : τ (b : ↥K) ∈ B, (⟨τ (b : ↥K), hBW _ hb⟩ : ↥W) ∈ maximalIdeal ↥W) →
        algebraMap A ↥B ϖ ∣ b) ∧

      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
        ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
            (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
          (∀ (b : ↥(chartAlgFin A (↥K) j)) (hb : τ (b : ↥K) ∈ chartAlgFin A (↥K) j),
              b ∈ y ↔ (⟨τ (b : ↥K), hb⟩ : ↥(chartAlgFin A (↥K) j)) ∈ y) →
          ∀ f : ↥K, f ∈ W ↔ τ f ∈ W))

    (n : ℕ) (hn1 : 1 ≤ n) (hnq : n ∣ q + 1)
    (γ₀ : SL(2, ℤ)) (hγ₀q : γ₀ ∈ CongruenceSubgroup.Gamma q) (hγ₀M : γ₀ ∈ CongruenceSubgroup.Gamma0 M')
    (τ₀ : ↥K ≃ₐ[L] ↥K) (hτ₀ : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') γ₀⁻¹ K τ₀)
    (hτ₀W : ∀ f : ↥K, f ∈ W ↔ τ₀ f ∈ W)
    (hcyc1 : ∀ f : ↥K, f ∈ B → (τ₀ ^ n) f = f)
    (hcyc2 : ∀ k : ℕ, 0 < k → k < n → ∃ f : ↥K, f ∈ B ∧ (τ₀ ^ k) f ≠ f)

    (m : ℕ) (hm1 : 1 ≤ m) (hmt : ∃ w : A, IsUnit w ∧ ϖ ^ m = ϖt * w)
    (O : Subring ↥K)
    (hO : (∃ (a : ↥(chartAlgFin A (↥K) j)) (_ : a ∈ J) (_ : ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) ≠ 0),
            let Ba : Subalgebra A ↥K := (Algebra.adjoin ↥(chartAlgFin A (↥K) j)
              {x : ↥K | ∃ i ∈ J, x * ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}).restrictScalars A
            ∃ (P : Ideal ↥Ba) (_ : P.IsMaximal),
              (∀ f : ↥K, f ∈ O ↔ ∃ g h : ↥Ba, h ∉ P ∧ f * (h : ↥K) = (g : ↥K)) ∧
              (∀ b : ↥(chartAlgFin A (↥K) j), b ∈ y →
                ∀ hb : ((b : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ O, ¬ IsUnit (⟨((b : ↥(chartAlgFin A (↥K) j)) : ↥K), hb⟩ : ↥O)) ∧
              ¬ (∀ f : ↥K, f ∈ B → f ∈ O)))
    (hOτ : ∀ f : ↥K, f ∈ O ↔ τ₀ f ∈ O) :
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
        (∃ (ζ₀ : (AdicCompletion (maximalIdeal A) A)) (_ : ζ₀ ^ n = 1) (_ : ∀ k : ℕ, 0 < k → k < n → IsUnit (ζ₀ ^ k - 1)),

          (∀ f : ↥K, f ∈ O → f ∈ W) ∧ ∃ (_ : IsLocalRing ↥O) (_ : IsNoetherianRing ↥O),
          (∀ b : ↥(chartAlgFin A (↥K) j), (b : ↥K) ∈ O) ∧
          (∀ x : L, algebraMap L ↥K x ∈ O ↔ ∃ a : A, algebraMap A L a = x) ∧
          (∀ (f : ↥K) (hf : f ∈ O), ∃ (a : A) (ha : algebraMap A ↥K a ∈ O), ¬ IsUnit ((⟨f, hf⟩ : ↥O) - ⟨_, ha⟩)) ∧

          (∃ (hϖO : algebraMap A ↥K ϖ ∈ O) (cx cy : ↥O) (u : (↥O)ˣ) (ι : (AdicCompletion (maximalIdeal ↥O) ↥O) ≃+* (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)))
             (γU γV : (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m))ˣ) (θ₀ : (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)) ≃ₐ[(AdicCompletion (maximalIdeal A) A)] (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m))) (ζ₀' : (AdicCompletion (maximalIdeal A) A)) (_ : ζ₀ * ζ₀' = 1)
             (_ : IsLocalRing (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m))),
            cx * cy = (⟨_, hϖO⟩ : ↥O) ^ m * (u : ↥O) ∧
            (∀ (a : A) (ha : algebraMap A ↥K a ∈ O), ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨_, ha⟩) = UVCrossingModel.const ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) (algebraMap A (AdicCompletion (maximalIdeal A) A) a)) ∧
            ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) cx) = (γU : (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m))) * UVCrossingModel.U ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) ∧
            ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) cy) = (γV : (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m))) * UVCrossingModel.V ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) ∧
            (∀ hcy : (cy : ↥K) ∈ W, (⟨(cy : ↥K), hcy⟩ : ↥W) ∈ maximalIdeal ↥W) ∧
            (∀ hcx : (cx : ↥K) ∈ W, (⟨(cx : ↥K), hcx⟩ : ↥W) ∉ maximalIdeal ↥W) ∧
            (∀ (f : ↥K) (hf : f ∈ O) (hf' : τ₀ f ∈ O),
              ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨_, hf'⟩) = θ₀ (ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨f, hf⟩))) ∧
            θ₀ (UVCrossingModel.U ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)) - UVCrossingModel.const ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) ζ₀ * UVCrossingModel.U ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) ∈
              (maximalIdeal (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m))) ^ 2 ∧
            θ₀ (UVCrossingModel.V ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)) - UVCrossingModel.const ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) ζ₀' * UVCrossingModel.V ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) ∈
              (maximalIdeal (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m))) ^ 2 ∧

            (∀ (c : W₁) (θ : S ≃+* S) (Mx : Matrix (Fin 2) (Fin 2) W₁)
                (hpres : ∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
                  τ₀ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
              (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                θ (e₁ (toC (germY a))) = e₁ (toC (germY (((τ₀ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                  (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a)))) →
              (∀ w : W₁, θ (mkS (MvPowerSeries.C w)) = mkS (MvPowerSeries.C w)) →
              (∀ jj : Fin 2, θ (mkS (MvPowerSeries.X jj)) -
                  mkS (∑ ii : Fin 2, MvPowerSeries.C (Mx ii jj) * MvPowerSeries.X ii) ∈
                (Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2) →
              (∀ ii jj : Fin 2, Mx ii jj - c * ((γ₀ ii jj : ℤ) : W₁) ∈ IsLocalRing.maximalIdeal W₁) →
              ∀ a : A, c - σ₁ a ∈ IsLocalRing.maximalIdeal W₁ →
                ¬ IsUnit (ζ₀' - algebraMap A (AdicCompletion (maximalIdeal A) A) a)))) := by sorry
