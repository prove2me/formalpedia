-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_forall_aeval_jqNModC_mem_maximalIdeal_of_igusaBranch_linked_of_dvd
-- name    : ModularCurve.FullLevel.AuxLevelOne.forall_aeval_jqNModC_mem_maximalIdeal_of_igusaBranch_linked_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:14.444979+00:00
-- url     : https://prove2.me/theorems/b6d3751e-11e9-51d7-912f-80b96b82afbd
-- title:
--   Residual transcendence of j(mathsf q^q) along an Igusa branch
-- statement:
--   **Level and coefficient data.** Fixed are: a prime $q$; a nonzero natural number $M'$ with $q \nmid M'$ (`hqM'`); a prime $\ell$ with $\ell \equiv 11 \pmod{12}$ (`hℓ12`) and $\ell \mid M'$ (`hℓM'`); a field $L$ of characteristic zero and a primitive $q$-th root of unity $\zeta \in L$; the hypothesis `hι` that some ring homomorphism $\iota : L \to \mathbb C$ satisfies $\iota\zeta = e^{2\pi i /q}$. The level subgroup $H_1 \le (\mathbb Z/q^2M')^\times$ is, by `hH₁`, the intersection of [`ModularCurve.FullLevel.levelH q M'`](def/ModularCurve_FullLevelJacobian.html#L22) — the kernel of the reduction $(\mathbb Z/q^2M')^\times \to (\mathbb Z/q)^\times$ — with the kernel of the reduction $(\mathbb Z/q^2M')^\times \to (\mathbb Z/\ell)^\times$; so $H_1$ consists of the units congruent to $1$ modulo $q$ and modulo $\ell$. The field $K$ is, by `hK`, [`ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField (q ^ 2 * M') H₁)`](def/ModularCurve_LaurentCoeff.html#L103): the intermediate field of $L \subset L((\mathsf q))$ generated over $L$ by the image under the coefficientwise map [`ModularCurve.coeffEmb`](def/ModularCurve_LaurentCoeff.html#L81) of the field of $\mathsf q$-expansions of modular functions of level $\Gamma_{H_1}(q^2M')$ over $\mathbb Q$.
--
--   The coefficient ring $A$ is a Henselian discrete valuation domain with fraction field $L$, with algebraically closed residue field, with $q \in \mathfrak m_A$ (`hAq`) and with $\zeta$ in the image of $A$ (`hζA`), and $K$ is an $A$-algebra compatibly with $L$. The element $j \in K$ is nonzero and has Laurent series `coeffEmb L ModularCurve.jq` (`hj`), the $\mathsf q$-expansion of the modular $j$-function. Further, $\varpi$ generates $\mathfrak m_A$ (`hϖ`), and $\varpi_t \in A$ satisfies $\varpi_t^{\,q^2-1} = q u$ with $u$ a unit (`hϖt`). Throughout, `chartAlgFin A K j` denotes the $A$-subalgebra of $K$ of elements integral over $A[j]$, `XFin` its spectrum, and [`AlgebraicCurve.TwoChartIntegralModel A K j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) the scheme obtained by glueing the spectra of the $j$-chart and the $j^{-1}$-chart algebras, with `ιFin` the $j$-chart immersion and `toBase` the structure morphism to $\operatorname{Spec} A$.
--
--   **The supersingular point.** $y$ is a maximal ideal of `chartAlgFin A K j` (`hy`) containing the image of $\varpi$ (`hϖy`), and `hss` requires that for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi$ from the chart algebra to $\Omega$ with kernel $y$, the value $\varphi(j)$ lies in [`ModularCurve.ssJSet q Ω`](def/ModularCurve_SupersingularModuli.html#L7), i.e. every elliptic curve over $\Omega$ with that $j$-invariant has no nonzero point killed by $q$.
--
--   **The rigidity package `hArig`.** This hypothesis asserts, for every point $z$ of the two-chart model at which the germ $\varpi_z$ of $\varpi$ (pulled back from the base, `hϖz`) lies in the maximal ideal of the stalk (`hz`), and every point $y'$ of `XFin` mapping to $z$ (`hy'`) at which the same supersingularity condition holds (`hss'`), the existence of: a complete discrete valuation domain $W$, a homomorphism $\sigma : A \to W$ with $\mathfrak m_W = (\sigma\varpi)$, power series $f, u, v \in W[[X_0,X_1]]$ with $u, v$ units and $f \equiv X_0X_1^q - X_0^qX_1$ modulo $(X_0,X_1)^{q+2}$ (the Drinfeld form [`DrinfeldCurve.LocalChart.drinfeldForm`](def/DrinfeldCurve_LocalChart.html#L18)), and a ring isomorphism $e$ from the adic completion of the stalk at $z$ onto $S := W[[X_0,X_1]]/\bigl(C(\sigma(\varpi_t^{\,q+1}))v - fu\bigr)$, such that seven clauses hold, written in terms of the completion map $\mathrm{toC}$, the quotient map $\mathrm{mkS}$ and the germ map $\mathrm{germY}$ from the chart algebra to the stalk at $z$ through $y'$ (these abbreviations are introduced in the statement itself): (1) $e$ carries the germ of a constant $a \in A$ to the class of $C(\sigma a)$; (2) for $\gamma \in \Gamma_0(M')$ and every $L$-automorphism $\tau$ of $K$ with `IsLevelAutAt L q ζ q (q^2*M') H₁ γ⁻¹ K τ` — that is, $\tau$ acts on the $\mathsf q$-expansions of quotients of modular forms of level $\Gamma_{H_1}(q^2M')$ by the substitution attached to the matrix `conjElemN q γ⁻¹`, normalised through any embedding $\iota$ with $\iota\zeta = e^{2\pi i/q}$ — the chart algebra is $\tau$-stable; (3) if moreover $\gamma_{11} \equiv 1 \pmod \ell$, then such a $\tau$ fixes $y'$ residually, $\tau(a) - a \in y'$ for all chart elements $a$; (4) for $\gamma \in \Gamma_0(M')$ and $\tau$ as above fixing $y'$ residually there exist a ring automorphism $\theta$ of $S$, $c \in W$ and $M \in M_2(W)$ with: $\theta$ conjugate to $\tau$ through $e \circ \mathrm{toC} \circ \mathrm{germY}$, $\theta$ fixing the constants, $\theta(X_{j}) \equiv \sum_i M_{ij}X_i$ modulo the square of the ideal generated by the classes of $X_0, X_1$, $c^{q+1} \equiv 1$ and $M_{ij} \equiv c\,\gamma_{ij}$ modulo $\mathfrak m_W$, $c \equiv 1$ modulo $\mathfrak m_W$ whenever $\gamma_{11} \equiv 1 \pmod \ell$, and $c \not\equiv 1$ whenever $\gamma \in \Gamma(q)$ and $\tau \neq \mathrm{id}$; (5) for integers $a_1,b_1,a_2,b_2$ and primes $P_1, P_2$ of $S$, each omitting one of the classes of $X_0, X_1$, each containing the class of $C(\sigma\varpi)$ and containing an element $a_iX_0 + b_iX_1 + h$ with $h \in (X_0,X_1)^2$, and with $q \nmid a_1b_2 - a_2b_1$, the contractions of $P_1$ and $P_2$ to the stalk differ; (6) for a prime $P$ of $S$ omitting one of the classes of $X_0, X_1$, containing the class of $C(\sigma\varpi)$ and containing $X_0 + h$ with $h \in (X_0,X_1)^2$, a chart element $a$ has its germ in the contraction of $P$ if and only if every Laurent coefficient of $a$ lies in the image of $\mathfrak m_A$; (7) the Igusa-branch clause: [`ModularCurve.jqNModC L q`](def/ModularCurve_JqCoeff.html#L18), the series obtained from the $j$-expansion over $L$ by multiplying all exponents by $q$, lies in $K$ and in the chart algebra, and there are $a_0 \in A$ with $j(\mathsf q^{q}) - a_0 \in y'$, an integer $e_0 \ge 1$ and $h \in (X_0,X_1)^{e_0}$ whose degree-$e_0$ form $\sum_{i\le e_0} h_{(i,e_0-i)}a^ib^{e_0-i}$ is a unit for every $a,b \in W$ not both in $\mathfrak m_W$ with $a^qb - ab^q \in \mathfrak m_W$, such that $e(\mathrm{toC}(\mathrm{germY}(j(\mathsf q^{q}) - a_0))) = \mathrm{mkS}\,h$.
--
--   **A chosen point and a chosen presentation.** Fixed are $z$, $\varpi_z$ with `hϖz`, `hz`, a point $y'$ of `XFin` over $z$ (`hy'`) satisfying the supersingularity condition `hss'` and with $y'$ the ideal $y$ (`hy'y`); and a complete discrete valuation domain $W_1$ with $\sigma_1$, $f_1, u_1, v_1$, the unit and congruence conditions `hu₁`, `hv₁`, `hf₁`, and an isomorphism $e_1$ of the completed stalk with $S = W_1[[X_0,X_1]]/(C(\sigma_1(\varpi_t^{q+1}))v_1 - f_1u_1)$, for which the hypothesis `hW₁` asserts all seven clauses listed above (for this data).
--
--   **The blow-up algebra and the Drinfeld reduction.** $J$ is the ideal of the chart algebra given by `hJ` as the infimum, over all $\gamma \in \Gamma(q) \cap \Gamma_0(M')$ and all level automorphisms $\tau$ at $\gamma^{-1}$ preserving the chart algebra, of the pullback along $\tau$ of the contraction, along $e_1 \circ \mathrm{toC} \circ \mathrm{germY}$, of the ideal of $S$ generated by the classes of $C(\sigma_1\varpi_t)$, $X_0$ and $X_1$. The algebra $B$ is, by `hB`, the $A$-subalgebra of $K$ obtained by adjoining to the chart algebra all $x \in K$ with $x\varpi_t \in J$. $W$ is a valuation subring of $K$ containing $B$ (`hBW`), and there are four groups of conditions: `hR1` (the chart algebra is contained in $B$, and $K$ is the fraction field of $B$); `hR2` ($B$ is formally smooth and of finite presentation over $A$, and $B/\varpi B$ has Krull dimension at most one); `hR3` (five clauses: $W \cap L$ is the image of $A$; $\mathfrak m_W$ is generated by $\varpi$; $W$ is a discrete valuation ring; $y$ is the centre of $W$ on the chart algebra; and $W$ is the localisation of $B$ at that centre); and `hEQ` (five clauses, summarised here: for every $\mathbb F_{q^2}$-algebra structure on the residue field of $A$ there is a surjection $\rho$ from $B$ onto the Drinfeld coordinate ring [`DrinfeldCurve.CoordRing q (ResidueField A)`](def/DrinfeldCurve_CoordRing.html#L21) with kernel the centre of $W$, compatible with the $A$-structure, and equivariant for level automorphisms through [`DrinfeldCurve.hAction`](def/DrinfeldCurve_CoordRing.html#L325) with a scalar $c \in \mathbb F_{q^2}^\times$ such that $(\gamma \bmod q, c)$ lies in the kernel `hSubgroup q` of $(g,c) \mapsto \det(g)c^{q+1}$, with $c \neq 1$ when $\gamma \in \Gamma(q)$ and $\tau \neq \mathrm{id}$; $B$ is stable under all level automorphisms at $\gamma^{-1}$ for $\gamma \in \Gamma_0(M')$; every prime of $B$ containing $\varpi$ is obtained by transporting the centre of $W$ by some level automorphism at $\gamma^{-1}$ with $\gamma \in \Gamma(q) \cap \Gamma_0(M')$; an element of $B$ lying in the centre of $W$ after every such transport is divisible by $\varpi$; and a level automorphism preserving $y$ on the chart algebra preserves $W$).
--
--   **The end $O$.** Fixed are the memberships `hjK`, `hjC` of $j(\mathsf q^{q})$ in $K$ and in the chart algebra; an integer $m \ge 1$ with $\varpi^m = \varpi_t w$, $w$ a unit (`hmt`); and a finite set `ends` of subrings of $K$ characterised by `hends`: $O \in$ `ends` if and only if there is a nonzero $a \in J$ such that, with $B_a$ the $A$-subalgebra obtained by adjoining to the chart algebra all $x$ with $xa \in J$, there is a maximal ideal $P$ of $B_a$ with $O$ the localisation of $B_a$ at $P$, every element of $y$ a non-unit in $O$, and $B$ not contained in $O$. One such $O$ is fixed (`hOmem`), together with: $O \subseteq W$ (`hOW`), $O$ local (`hOloc`) and Noetherian (`hOnoe`), the chart algebra contained in $O$ (`hCO`), $\varpi \in O$ (`hϖO`); elements $c_x, c_y \in O$, a unit $u$ of $O$ with $c_xc_y = \varpi^m u$ (`hcxy`); an isomorphism $\iota$ of the adic completion of $O$ with the crossing model `UVCrossingModel` $\hat A[[U,V]]/(UV - \varpi^m)$ over the completion of $A$, taking constants from $A$ to constants (`hιc`) and $c_x$, $c_y$ to $\gamma_U U$ and $\gamma_V V$ for units $\gamma_U, \gamma_V$ (`hιx`, `hιy`); and $c_y$ in the centre of $W$ (`hcyW`) while $c_x$ is not (`hcxW`).
--
--   **The valuation ring $W_x$.** Finally, $W_x$ is a valuation subring of $K$ containing the chart algebra (`hB1`), with $W_x \cap L$ the image of $A$ (`hB2`), with $\mathfrak m_{W_x}$ generated by $\varpi$ (`hB4`), such that every chart element lying in $\mathfrak m_{W_x}$ lies in $y$ (`hB9`), and such that some element of $y$ does not lie in $\mathfrak m_{W_x}$ (`hB10`).
--
--   **Conclusion.** Two assertions hold. First, there exists $t \in W_x$ such that for every polynomial $p \in A[X]$, if the value at $t$ of the polynomial obtained from $p$ by the structure map $A \to L$ lies in $W_x$ and in $\mathfrak m_{W_x}$, then every coefficient of $p$ lies in $\mathfrak m_A$. Second, the same conclusion holds for the specific element $j(\mathsf q^{q}) =$ [`ModularCurve.jqNModC L q`](def/ModularCurve_JqCoeff.html#L18) of $K$: for every $p \in A[X]$, if the value of $p$ at this element lies in $W_x$ and in $\mathfrak m_{W_x}$, then all coefficients of $p$ lie in $\mathfrak m_A$. No monicity is assumed of $p$ in either conjunct; the first conjunct is the bare existence statement implied by the second.
--
--   The statement expresses that the moduli invariant $j(\mathsf q^{q})$ is residually transcendental for a valuation $W_x$ whose centre on the $j$-chart algebra is contained in, but differs from, the supersingular maximal ideal $y$ — the characteristic property of the Igusa component through a supersingular point on the blow-up of the tame node. It is one step in the construction of the Igusa valuation subring attached to an end of the blow-up chart, and is cited by [`ModularCurve.FullLevel.AuxLevelOne.exists_igusaValuationSubring_of_mem_ends_blowupChart_of_drinfeldChartWitness_linked_of_dvd`](thm.html#ModularCurve.FullLevel.AuxLevelOne.exists_igusaValuationSubring_of_mem_ends_blowupChart_of_drinfeldChartWitness_linked_of_dvd); the present version works with the auxiliary level $\Gamma_{H_1}(q^2M')$ and the diamond condition $\gamma_{11} \equiv 1 \bmod \ell$ in place of a full auxiliary level, and imposes no lower bound on $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevelOne_forall_aeval_jqNModC_mem_maximalIdeal_of_igusaBranch_linked_of_dvd.lean

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

theorem ModularCurve.FullLevel.AuxLevelOne.forall_aeval_jqNModC_mem_maximalIdeal_of_igusaBranch_linked_of_dvd
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
                  (((γ 1 1 : ℤ) : ZMod ℓ) = 1 → c - 1 ∈ IsLocalRing.maximalIdeal W) ∧

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

        (∃ (hjK : ModularCurve.jqNModC L q ∈ K)
           (hjC : (⟨ModularCurve.jqNModC L q, hjK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
           (a₀ : A) (_ : (⟨(⟨ModularCurve.jqNModC L q, hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) -
              algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a₀ ∈ y'.asIdeal)
           (e₀ : ℕ) (_ : 1 ≤ e₀) (h : MvPowerSeries (Fin 2) W)
           (_ : h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ e₀),
           (∀ a b : W, (a ∉ IsLocalRing.maximalIdeal W ∨ b ∉ IsLocalRing.maximalIdeal W) →
              a ^ q * b - a * b ^ q ∈ IsLocalRing.maximalIdeal W →
              IsUnit (∑ i ∈ Finset.range (e₀ + 1),
                MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (e₀ - i)) h * a ^ i * b ^ (e₀ - i))) ∧
           (e : CMP →+* S) (toC (germY ((⟨(⟨ModularCurve.jqNModC L q, hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) -
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
            ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
              (∀ f : ↥K, f ∈ W ↔ τ f ∈ W) →
              ∃ (c : (GaloisField q 2)ˣ) (hmem : (ModularCurve.FullLevel.redQ q γ, c) ∈ DrinfeldCurve.hSubgroup q),
                (∀ (b : ↥B) (hb : τ (b : ↥K) ∈ B), ρ ⟨τ (b : ↥K), hb⟩ = DrinfeldCurve.hAction q (ResidueField A) ⟨_, hmem⟩ (ρ b)) ∧
                (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥K, τ k = k) → c ≠ 1))) ∧

      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
        ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
          ∀ f : ↥K, f ∈ B → τ f ∈ B) ∧
      (∀ Q : Ideal ↥B, Q.IsPrime → algebraMap A ↥B ϖ ∈ Q →
        ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧
          ∃ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ ∧
            ∀ b : ↥B, (⟨(b : ↥K), hBW _ b.2⟩ : ↥W) ∈ maximalIdeal ↥W → τ (b : ↥K) ∈ B ∧ ∀ hb : τ (b : ↥K) ∈ B, (⟨τ (b : ↥K), hb⟩ : ↥B) ∈ Q) ∧
      (∀ b : ↥B, (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
            ∀ hb : τ (b : ↥K) ∈ B, (⟨τ (b : ↥K), hBW _ hb⟩ : ↥W) ∈ maximalIdeal ↥W) →
        algebraMap A ↥B ϖ ∣ b) ∧

      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
        ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
          (∀ (b : ↥(chartAlgFin A (↥K) j)) (hb : τ (b : ↥K) ∈ chartAlgFin A (↥K) j),
              b ∈ y ↔ (⟨τ (b : ↥K), hb⟩ : ↥(chartAlgFin A (↥K) j)) ∈ y) →
          ∀ f : ↥K, f ∈ W ↔ τ f ∈ W))

    (hjK : ModularCurve.jqNModC L q ∈ K)
    (hjC : (⟨ModularCurve.jqNModC L q, hjK⟩ : ↥K) ∈ chartAlgFin A (↥K) j)

    (m : ℕ) (hm1 : 1 ≤ m) (hmt : ∃ w : A, IsUnit w ∧ ϖ ^ m = ϖt * w)

    (ends : Finset (Subring ↥K))
    (hends : ∀ O : Subring ↥K, O ∈ ends ↔
      ∃ (a : ↥(chartAlgFin A (↥K) j)) (_ : a ∈ J) (_ : ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) ≠ 0),
      let Ba : Subalgebra A ↥K := (Algebra.adjoin ↥(chartAlgFin A (↥K) j)
        {x : ↥K | ∃ i ∈ J, x * ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}).restrictScalars A
      ∃ (P : Ideal ↥Ba) (_ : P.IsMaximal),
        (∀ f : ↥K, f ∈ O ↔ ∃ g h : ↥Ba, h ∉ P ∧ f * (h : ↥K) = (g : ↥K)) ∧
        (∀ b : ↥(chartAlgFin A (↥K) j), b ∈ y →
          ∀ hb : ((b : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ O, ¬ IsUnit (⟨((b : ↥(chartAlgFin A (↥K) j)) : ↥K), hb⟩ : ↥O)) ∧
        ¬ (∀ f : ↥K, f ∈ B → f ∈ O))
    (O : Subring ↥K) (hOmem : O ∈ ends)

    (hOW : ∀ f : ↥K, f ∈ O → f ∈ W) (hOloc : IsLocalRing ↥O) (hOnoe : IsNoetherianRing ↥O)
    (hCO : ∀ b : ↥(chartAlgFin A (↥K) j), (b : ↥K) ∈ O)

    (hϖO : algebraMap A ↥K ϖ ∈ O) (cx cy : ↥O) (u : (↥O)ˣ)
    (ι : (AdicCompletion (maximalIdeal ↥O) ↥O) ≃+* (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m)))
    (γU γV : (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m))ˣ)
    (hcxy : cx * cy = (⟨_, hϖO⟩ : ↥O) ^ m * (u : ↥O))
    (hιc : ∀ (a : A) (ha : algebraMap A ↥K a ∈ O), ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨_, ha⟩) = UVCrossingModel.const ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m) (algebraMap A (AdicCompletion (maximalIdeal A) A) a))
    (hιx : ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) cx) = (γU : (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m))) * UVCrossingModel.U ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m))
    (hιy : ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) cy) = (γV : (UVCrossingModel (AdicCompletion (maximalIdeal A) A) ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m))) * UVCrossingModel.V ((algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) ^ m))
    (hcyW : ∀ hcy : (cy : ↥K) ∈ W, (⟨(cy : ↥K), hcy⟩ : ↥W) ∈ maximalIdeal ↥W)
    (hcxW : ∀ hcx : (cx : ↥K) ∈ W, (⟨(cx : ↥K), hcx⟩ : ↥W) ∉ maximalIdeal ↥W)
    (Wx : ValuationSubring ↥K)
    (hB1 : (∀ b : ↥(chartAlgFin A (↥K) j), (b : ↥K) ∈ Wx))
    (hB2 : (∀ x : L, algebraMap L ↥K x ∈ Wx ↔ ∃ a : A, algebraMap A L a = x))
    (hB4 : (∃ hϖWx : algebraMap A ↥K ϖ ∈ Wx, maximalIdeal ↥Wx = Ideal.span {(⟨_, hϖWx⟩ : ↥Wx)}))
    (hB9 : (∀ b : ↥(chartAlgFin A (↥K) j), (∀ hb : (b : ↥K) ∈ Wx, (⟨(b : ↥K), hb⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) → b ∈ y))
    (hB10 : (∃ b : ↥(chartAlgFin A (↥K) j), b ∈ y ∧ ∀ hb : (b : ↥K) ∈ Wx, (⟨(b : ↥K), hb⟩ : ↥Wx) ∉ maximalIdeal ↥Wx)) :
    (∃ (t : ↥Wx), ∀ p : Polynomial A,
                (∃ hm : Polynomial.aeval (t : ↥K) (p.map (algebraMap A L)) ∈ Wx, (⟨_, hm⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) →
                  ∀ i, p.coeff i ∈ maximalIdeal A) ∧
    (∀ p : Polynomial A,
                (∃ hm : Polynomial.aeval (⟨ModularCurve.jqNModC L q, hjK⟩ : ↥K) (p.map (algebraMap A L)) ∈ Wx, (⟨_, hm⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) →
                  ∀ i, p.coeff i ∈ maximalIdeal A) := by sorry
