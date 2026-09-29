-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_exists_verticalUnit_chartAlgFin_mem_maximalIdeal_iff_of_end_blowupChart_of_dvd
-- name    : ModularCurve.FullLevel.AuxLevelOne.exists_verticalUnit_chartAlgFin_mem_maximalIdeal_iff_of_end_blowupChart_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:14.444979+00:00
-- url     : https://prove2.me/theorems/344a0f91-17c8-5cc7-be54-405a217ae43e
-- title:
--   Vertical Γ(q)-invariant unit in the weighted centre at an end
-- statement:
--   Throughout, $q$ and $\ell$ are primes, $M'$ is a nonzero natural number with $q \nmid M'$, and $\ell \equiv 11 \pmod{12}$ with $\ell \mid M'$. The field $L$ has characteristic zero, $\zeta \in L$ is a primitive $q$-th root of unity, and the hypothesis `hι` provides a ring homomorphism $\iota : L \to \mathbb{C}$ with $\iota\zeta = e^{2\pi i/q}$. The subgroup $H_1 \le (\mathbb{Z}/q^2M')^\times$ is required (`hH₁`) to be [`ModularCurve.FullLevel.levelH q M'`](def/ModularCurve_FullLevelJacobian.html#L22) intersected with the kernel of reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/\ell)^\times$; here `levelH q M'` is the kernel of the reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$, so $H_1$ consists of the units congruent to $1$ modulo $q$ and modulo $\ell$. The intermediate field $K$ between $L$ and $L((t))$ is required (`hK`) to be [`ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField (q ^ 2 * M') H₁)`](def/ModularCurve_LaurentCoeff.html#L103), i.e. the subfield generated over $L$ by the coefficientwise image of the $q$-expansion function field of the congruence subgroup $\Gamma_{H_1}(q^2M')$.
--
--   The base ring $A$ is a discrete valuation domain, henselian local, with algebraically closed residue field, equipped with an $A$-algebra structure on $L$ making $L$ its fraction field and with a compatible $A$-algebra structure on $K$; $q$ lies in $\mathfrak{m}_A$ (`hAq`) and $\zeta$ lies in the image of $A$ (`hζA`). The element $j \in K$ is nonzero and its Laurent expansion is the coefficientwise image of the classical expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) (`hj`). The element $\varpi$ generates $\mathfrak m_A$ (`hϖ`), and $\varpi_t \in A$ satisfies $\varpi_t^{\,q^2-1} = q u$ for some unit $u$ (`hϖt`).
--
--   Write $C :=$ `chartAlgFin A K j`, the $A$-subalgebra of elements of $K$ integral over $A[j]$, with distinguished element `jChartFin A K j` $= j$, and write $X :=$ [`AlgebraicCurve.TwoChartIntegralModel A K j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) for the scheme obtained as the pushout gluing $\operatorname{Spec}$ of the $j$-chart algebra and $\operatorname{Spec}$ of the $j^{-1}$-chart algebra along the middle chart, with its structural morphism `toBase` to $\operatorname{Spec} A$ and the canonical morphism `ιFin` from $X_{\mathrm{Fin}} = \operatorname{Spec} C$. The ideal $y \subset C$ is maximal (`hy`), contains the image of $\varpi$ (`hϖy`), and is supersingular in the sense of `hss`: for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi : C \to \Omega$ with kernel $y$, the element $\varphi(j)$ lies in [`ModularCurve.ssJSet q Ω`](def/ModularCurve_SupersingularModuli.html#L7), the set of those $j_0 \in \Omega$ such that every elliptic curve over $\Omega$ with $j$-invariant $j_0$ has no nonzero $q$-torsion point.
--
--   For $\gamma \in \mathrm{SL}_2(\mathbb{Z})$, an $L$-algebra automorphism $\tau$ of $K$ is called below a *level automorphism attached to* $\gamma^{-1}$ when [`ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ`](def/ModularCurve_FullLevelLevelAutAt.html#L29) holds, that is: for every weight $k$, all modular forms $f, g$ of weight $k$ on the subgroup [`CohCarrier.GammaH (q ^ 2 * M') H₁`](def/CohCarrier_Level.html#L133) of $\mathrm{GL}_2(\mathbb{R})$ admitting integral $q$-expansions $p_f, p_g$ with the Laurent series of $p_g$ nonzero, every $x \in K$ whose Laurent expansion is the image under `coeffEmb` of $p_f/p_g$, and every $\iota : L \to \mathbb{C}$ with $\iota\zeta = e^{2\pi i /q}$, the product of the coefficientwise $\iota$-image of the expansion of $\tau x$ with the $q$-expansion of $g \mid_k \mathrm{conjElemN}\, q\, \gamma^{-1}$ equals the $q$-expansion of $f \mid_k \mathrm{conjElemN}\, q\, \gamma^{-1}$, where $\mathrm{conjElemN}\,q\,\delta$ is the matrix with rows $(\delta_{00}, \delta_{01}/q)$ and $(q\,\delta_{10}, \delta_{11})$.
--
--   The hypothesis `hArig` is a uniform local-rigidity assumption at supersingular points: for every point $z$ of $X$, every element $\varpi_z$ of the stalk at $z$ equal to the germ of the image of $\varpi$ under `toBase`, lying in the maximal ideal of that stalk, and every point $y'$ of $\operatorname{Spec} C$ with `ιFin` $(y') = z$ whose prime satisfies the same supersingularity condition as in `hss`, there exist a complete discrete valuation domain $W$, a ring homomorphism $\sigma : A \to W$ with $\mathfrak m_W = (\sigma\varpi)$, power series $f, u, v \in W[[X_0,X_1]]$ with $u, v$ units and $f \equiv X_0X_1^q - X_0^qX_1$ modulo $(X_0,X_1)^{q+2}$ (the comparison form being [`DrinfeldCurve.LocalChart.drinfeldForm q W`](def/DrinfeldCurve_LocalChart.html#L18)), and a ring isomorphism $e$ from the adic completion of the stalk at $z$ onto $S := W[[X_0,X_1]]/(\sigma(\varpi_t^{\,q+1})v - fu)$, such that, writing $\mathrm{toC}$ for the map to the completion, $\mathrm{mkS}$ for the quotient map and $\mathrm{germY}$ for the composite $C \to \mathcal{O}_{X,z}$ through `ιFin`, the following seven clauses hold: (i) $e$ carries the germ of the image of $a \in A$ to the class of the constant $\sigma(a)$; (ii) every level automorphism attached to $\gamma^{-1}$, for $\gamma \in \Gamma_0(M')$, maps $C$ into $C$; (iii) for $\gamma \in \Gamma_0(M')$ with $\gamma_{11} \equiv 1 \pmod \ell$, every such $\tau$ preserving $C$ induces on $C$ a map congruent to the identity modulo $y'$; (iv) for $\gamma \in \Gamma_0(M')$ and $\tau$ attached to $\gamma^{-1}$, preserving $C$ and inducing the identity modulo $y'$, there exist a ring automorphism $\theta$ of $S$, an element $c \in W$ and a matrix $M \in M_2(W)$ with $\theta$ compatible with the action of $\tau$ on $C$ through $e \circ \mathrm{toC} \circ \mathrm{germY}$, $\theta$ fixing all constants, $\theta(X_j) \equiv \sum_i M_{ij}X_i$ modulo the square of the ideal generated by the classes of $X_0, X_1$, $c^{q+1} \equiv 1$ and $M_{ij} \equiv c\,\gamma_{ij}$ modulo $\mathfrak m_W$, with $c \equiv 1 \pmod{\mathfrak m_W}$ whenever $\gamma_{11} \equiv 1 \pmod \ell$, and $c - 1 \notin \mathfrak m_W$ whenever $\gamma \in \Gamma(q)$ and $\tau \ne \mathrm{id}$; (v) for integers $a_1,b_1,a_2,b_2$ and primes $P_1, P_2$ of $S$, each missing one of the classes of $X_0, X_1$, each containing the class of $\sigma\varpi$ and each containing an element $a_iX_0 + b_iX_1 + h$ with $h \in (X_0,X_1)^2$, if $q \nmid a_1b_2 - a_2b_1$ then the contractions of $P_1$ and $P_2$ along $e \circ \mathrm{toC}$ differ; (vi) for a prime $P$ of $S$ missing one of the classes of $X_0, X_1$, containing the class of $\sigma\varpi$ and containing an element $X_0 + h$ with $h \in (X_0,X_1)^2$, an element $a \in C$ has $\mathrm{toC}(\mathrm{germY}(a))$ in the contraction of $P$ along $e$ if and only if every Laurent coefficient of $a$ lies in the image of $\mathfrak m_A$ in $L$; (vii) [`ModularCurve.jqNModC L q`](def/ModularCurve_JqCoeff.html#L18) (the Laurent expansion of $j$ with its exponents scaled by $q$) lies in $K$ and in $C$, and there are $a_0 \in A$ with the class of this element minus $a_0$ in $y'$, an integer $e_0 \ge 1$ and $h \in (X_0,X_1)^{e_0}$ such that $\sum_{i=0}^{e_0} \mathrm{coeff}_{(i,\,e_0-i)}(h)\,a^ib^{e_0-i}$ is a unit of $W$ for all $a, b \in W$ not both in $\mathfrak m_W$ with $a^qb - ab^q \in \mathfrak m_W$, and $e(\mathrm{toC}(\mathrm{germY}(\mathrm{jqNModC} - a_0)))$ equals the class of $h$.
--
--   A point $z$ of $X$, an element $\varpi_z$ as above lying in the maximal ideal of the stalk, a point $y'$ of $\operatorname{Spec} C$ above $z$ satisfying the supersingularity condition `hss'`, and the identification $y' = y$ (`hy'y`) are then fixed, together with one instance $(W_1, \sigma_1, f_1, u_1, v_1, e_1)$ of the data above for this $z$ and $y'$ — $W_1$ a complete discrete valuation domain, $\mathfrak m_{W_1} = (\sigma_1\varpi)$, $u_1, v_1$ units, $f_1 \equiv X_0X_1^q - X_0^qX_1$ modulo $(X_0,X_1)^{q+2}$, and $e_1$ an isomorphism of the completed stalk with $S_1 := W_1[[X_0,X_1]]/(\sigma_1(\varpi_t^{q+1})v_1 - f_1u_1)$ — and with the hypothesis `hW₁` asserting for this instance exactly the seven clauses (i)–(vii) just listed.
--
--   The remaining data are: the ideal $J \subset C$, required by `hJ` to be the infimum, over all $\gamma \in \Gamma(q) \cap \Gamma_0(M')$ and all level automorphisms $\tau$ attached to $\gamma^{-1}$ that preserve $C$, of the pullback along $\tau|_C$ of the contraction along $e_1 \circ \mathrm{toC} \circ \mathrm{germY}$ of the ideal of $S_1$ generated by the classes of $\sigma_1\varpi_t$, $X_0$ and $X_1$; the $A$-subalgebra $B \subseteq K$ required by `hB` to be the $C$-algebra generated by $\{x \in K : \exists\, i \in J,\ x\varpi_t = i\}$, i.e. $C[J/\varpi_t]$; and a valuation subring $W \subseteq K$ containing $B$ (`hBW`). The hypothesis `hR1` has two clauses: $C \le B$, and every element of $K$ is a quotient of two elements of $B$ with nonzero denominator. The hypothesis `hR2` has three clauses: $A \to B$ is formally smooth, $A \to B$ is of finite presentation, and $B/(\varpi)$ has Krull dimension at most $1$. The hypothesis `hR3` has five clauses: an element of $L$ lies in $W$ exactly when it lies in the image of $A$; $\mathfrak m_W$ is generated by the image of $\varpi$; $W$ is a discrete valuation ring; an element of $C$ lies in $y$ exactly when it lies in $\mathfrak m_W$; and $W$ is the localisation of $B$ at that prime, in the sense that $f \in W$ exactly when $f = g/h$ with $g, h \in B$ and $h \notin \mathfrak m_W$.
--
--   The hypothesis `hEQ` has five clauses. First, for every $\mathrm{GF}(q^2)$-algebra structure on the residue field $k$ of $A$ there is a surjective ring homomorphism $\rho : B \to$ [`DrinfeldCurve.CoordRing q k`](def/DrinfeldCurve_CoordRing.html#L21) (the quotient of $k[X_0,X_1]$ by the ideal generated by `drinfeldPoly q k` $- 1$) whose kernel is the set of $b \in B$ lying in $\mathfrak m_W$, which is compatible with $A \to k$, and which is equivariant as follows: for $\gamma \in \Gamma_0(M')$ and $\tau$ attached to $\gamma^{-1}$ with $f \in W \iff \tau f \in W$, there is $c \in \mathrm{GF}(q^2)^\times$ with $(\mathrm{redQ}\,q\,\gamma, c)$ in [`DrinfeldCurve.hSubgroup q`](def/DrinfeldCurve_CoordRing.html#L276) (the kernel of the character sending $(g,c)$ to the product of the image of $\det g$ with $c^{q+1}$) such that $\rho(\tau b) =$ `hAction` of $(\mathrm{redQ}\,q\,\gamma, c)$ applied to $\rho(b)$, and $c \ne 1$ whenever $\gamma \in \Gamma(q)$ and $\tau \ne \mathrm{id}$. Second, every level automorphism attached to $\gamma^{-1}$ with $\gamma \in \Gamma_0(M')$ maps $B$ into $B$. Third, every prime $Q$ of $B$ containing the image of $\varpi$ arises from the special fibre by a translate: there are $\gamma \in \Gamma(q) \cap \Gamma_0(M')$ and $\tau$ attached to $\gamma^{-1}$ such that every $b \in B$ lying in $\mathfrak m_W$ has $\tau b \in B$ and $\tau b \in Q$. Fourth, if $b \in B$ is such that $\tau b$ lies in $\mathfrak m_W$ for all $\gamma \in \Gamma(q) \cap \Gamma_0(M')$ and all $\tau$ attached to $\gamma^{-1}$, then the image of $\varpi$ divides $b$ in $B$. Fifth, if $\gamma \in \Gamma_0(M')$ and $\tau$ attached to $\gamma^{-1}$ preserves $y$ on $C$ (in the stated two-sided sense), then $f \in W \iff \tau f \in W$.
--
--   Finally, $O$ is a subring of $K$ subject to `hO`: there are a nonzero $a \in J$ such that, setting $B_a := C[J/a]$ (the $C$-algebra generated by $\{x \in K : \exists\, i \in J,\ xa = i\}$), and a maximal ideal $P$ of $B_a$, such that $O$ is the localisation of $B_a$ at $P$ ($f \in O$ exactly when $f = g/h$ with $g,h \in B_a$, $h \notin P$), every element of $y$ that lies in $O$ is a non-unit of $O$, and $B$ is not contained in $O$. Further, $O \subseteq W$ (`hOW`), $O$ is local (`hOloc`) and Noetherian (`hOnoe`), $C \subseteq O$ (`hCO`), and the hypothesis `hIgStab` asserts that every valuation subring $V$ of $K$ whose intersection with $L$ is the image of $A$, for which the image of $\varpi$ lies in $\mathfrak m_V$, which contains $C$, and for which some $c \in C$ has $p(c)$ a unit of $V$ for every monic $p \in A[X]$, is stable under all level automorphisms attached to $\gamma^{-1}$ with $\gamma \in \Gamma(q) \cap \Gamma_0(M')$, in the sense that $f \in V \iff \tau f \in V$.
--
--   Under these hypotheses there exist $n \ge 1$ and $s \in J^n$ with nonzero image in $K$ such that:
--
--   (1) $s$ divides a power of $\varpi$ in $C$: there are $k \in \mathbb{N}$ and $z \in C$ with $s z = (\text{image of } \varpi)^k$;
--
--   (2) $s$ is invariant: $\tau(s) = s$ for every $\gamma \in \Gamma(q) \cap \Gamma_0(M')$ and every level automorphism $\tau$ attached to $\gamma^{-1}$;
--
--   (3) $\varpi_t^{\,n} s^{-1} \in W$;
--
--   (4) for every valuation subring $V$ of $K$ whose intersection with $L$ is the image of $A$ and in which the image of $\varpi$, if it lies in $V$ at all, lies in $\mathfrak m_V$: if $j \in V$, if $p(j)$ is a unit of $V$ whenever it lies in $V$ for every monic $p \in A[X]$, and if $O \subseteq V$, then $s$, whenever it lies in $V$, is a unit of $V$;
--
--   (5) for every valuation subring $V$ of $K$ satisfying the same two conditions on $L \cap V$ and on $\varpi$: if $j \in V$, if $p(j)$ is a unit of $V$ whenever it lies in $V$ for every monic $p \in A[X]$, and if some $f \in O$ does not lie in $V$, then there exists $c \in J^n$ with $c\,s^{-1} \notin V$.
--
--   This is a step in the local study of the blown-up supersingular chart of the integral two-chart model of the modular curve of level $\Gamma_{H_1}(q^2M')$, in the variant frame where the auxiliary full level is replaced by a diamond condition at a guard prime $\ell \equiv 11 \pmod{12}$ dividing $M'$, so that no lower bound on $q$ is needed. It produces the 'vertical unit' $s$ attached to an end $O$ of the blown-up chart: an invariant element of a power of the weighted centre $J$ which divides a power of the uniformiser, has prescribed order on the exceptional valuation, is a unit on every Igusa-type valuation containing the end, and is dominated by $J^n$ on the others; it is used by [`ModularCurve.FullLevel.AuxLevelOne.exists_verticalUnit_pow_centre_of_end_blowupChart_of_dvd`](thm.html#ModularCurve.FullLevel.AuxLevelOne.exists_verticalUnit_pow_centre_of_end_blowupChart_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevelOne_exists_verticalUnit_chartAlgFin_mem_maximalIdeal_iff_of_end_blowupChart_of_dvd.lean

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

theorem ModularCurve.FullLevel.AuxLevelOne.exists_verticalUnit_chartAlgFin_mem_maximalIdeal_iff_of_end_blowupChart_of_dvd
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
    (O : Subring ↥K)

    (hO : ∃ (a : ↥(chartAlgFin A (↥K) j)) (_ : a ∈ J) (_ : ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) ≠ 0),
      let Ba : Subalgebra A ↥K := (Algebra.adjoin ↥(chartAlgFin A (↥K) j)
        {x : ↥K | ∃ i ∈ J, x * ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}).restrictScalars A
      ∃ (P : Ideal ↥Ba) (_ : P.IsMaximal),
        (∀ f : ↥K, f ∈ O ↔ ∃ g h : ↥Ba, h ∉ P ∧ f * (h : ↥K) = (g : ↥K)) ∧
        (∀ b : ↥(chartAlgFin A (↥K) j), b ∈ y →
          ∀ hb : ((b : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ O, ¬ IsUnit (⟨((b : ↥(chartAlgFin A (↥K) j)) : ↥K), hb⟩ : ↥O)) ∧
        ¬ (∀ f : ↥K, f ∈ B → f ∈ O))

    (hOW : ∀ f : ↥K, f ∈ O → f ∈ W) (hOloc : IsLocalRing ↥O) (hOnoe : IsNoetherianRing ↥O)
    (hCO : ∀ b : ↥(chartAlgFin A (↥K) j), (b : ↥K) ∈ O)

    (hIgStab : ∀ V : ValuationSubring ↥K, (∀ x : L, algebraMap L ↥K x ∈ V ↔ ∃ a : A, algebraMap A L a = x) →
        (∃ hϖV : algebraMap A ↥K ϖ ∈ V, (⟨algebraMap A ↥K ϖ, hϖV⟩ : ↥V) ∈ maximalIdeal ↥V) →

        (∀ b : ↥(chartAlgFin A (↥K) j), (b : ↥K) ∈ V) →
        (∃ c : ↥(chartAlgFin A (↥K) j), ∀ p : Polynomial A, p.Monic →
          ∃ hp : Polynomial.aeval ((c : ↥K)) (p.map (algebraMap A ↥K)) ∈ V, (⟨_, hp⟩ : ↥V) ∉ maximalIdeal ↥V) →
        ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
            ∀ f : ↥K, f ∈ V ↔ τ f ∈ V) :

      ∃ (n : ℕ) (_ : 1 ≤ n) (s : ↥(chartAlgFin A (↥K) j)) (_ : s ∈ J ^ n) (_ : ((s : ↥(chartAlgFin A (↥K) j)) : ↥K) ≠ 0),

        (∃ (k : ℕ) (z : ↥(chartAlgFin A (↥K) j)), s * z = algebraMap A ↥(chartAlgFin A (↥K) j) ϖ ^ k) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ → τ ((s : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((s : ↥(chartAlgFin A (↥K) j)) : ↥K)) ∧

        algebraMap A ↥K ϖt ^ n * (((s : ↥(chartAlgFin A (↥K) j)) : ↥K))⁻¹ ∈ W ∧

        (∀ V : ValuationSubring ↥K, (∀ x : L, algebraMap L ↥K x ∈ V ↔ ∃ a : A, algebraMap A L a = x) →
          (∀ hϖV : algebraMap A ↥K ϖ ∈ V, (⟨algebraMap A ↥K ϖ, hϖV⟩ : ↥V) ∈ maximalIdeal ↥V) →
          (∀ hjV : (j : ↥K) ∈ V, (∀ p : Polynomial A, p.Monic →
          ∀ hp : Polynomial.aeval (j : ↥K) (p.map (algebraMap A ↥K)) ∈ V,
          (⟨_, hp⟩ : ↥V) ∉ maximalIdeal ↥V) →
          (∀ f : ↥K, f ∈ O → f ∈ V) → ∀ hs : ((s : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ V, (⟨_, hs⟩ : ↥V) ∉ maximalIdeal ↥V)) ∧

        (∀ V : ValuationSubring ↥K, (∀ x : L, algebraMap L ↥K x ∈ V ↔ ∃ a : A, algebraMap A L a = x) →
          (∀ hϖV : algebraMap A ↥K ϖ ∈ V, (⟨algebraMap A ↥K ϖ, hϖV⟩ : ↥V) ∈ maximalIdeal ↥V) →
          (∀ hjV : (j : ↥K) ∈ V, (∀ p : Polynomial A, p.Monic →
          ∀ hp : Polynomial.aeval (j : ↥K) (p.map (algebraMap A ↥K)) ∈ V,
          (⟨_, hp⟩ : ↥V) ∉ maximalIdeal ↥V) →
          (∃ f : ↥K, f ∈ O ∧ f ∉ V) → ∃ c : ↥(chartAlgFin A (↥K) j), c ∈ J ^ n ∧ ((c : ↥(chartAlgFin A (↥K) j)) : ↥K) * (((s : ↥(chartAlgFin A (↥K) j)) : ↥K))⁻¹ ∉ V)) := by sorry
