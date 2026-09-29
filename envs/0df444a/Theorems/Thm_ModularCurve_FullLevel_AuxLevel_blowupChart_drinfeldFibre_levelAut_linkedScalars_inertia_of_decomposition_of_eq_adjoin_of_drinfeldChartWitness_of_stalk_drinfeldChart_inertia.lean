-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevel_blowupChart_drinfeldFibre_levelAut_linkedScalars_inertia_of_decomposition_of_eq_adjoin_of_drinfeldChartWitness_of_stalk_drinfeldChart_inertia
-- name    : ModularCurve.FullLevel.AuxLevel.blowupChart_drinfeldFibre_levelAut_linkedScalars_inertia_of_decomposition_of_eq_adjoin_of_drinfeldChartWitness_of_stalk_drinfeldChart_inertia
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:14.444979+00:00
-- url     : https://prove2.me/theorems/427c9169-3ea9-5aae-a9c5-fab5634aacd9
-- title:
--   Tame inertia on the exceptional Drinfeld fibre
-- statement:
--   **Data.** Let $q\ge 5$ and $\ell\ge 3$ be primes with $\ell\neq q$, let $M'$ be a non-zero natural number with $q\nmid M'$ and $\ell\nmid M'$. Let $L$ be a field of characteristic zero and $\xi\in L$ a primitive $(q\ell)$-th root of unity; the hypothesis `hι` provides a ring homomorphism $\iota\colon L\to\mathbb{C}$ with $\iota\xi=\exp(2\pi i/(q\ell))$. Let $K$ be an intermediate field of $L\subseteq \mathrm{LaurentSeries}\,L$ with, by `hK`, $K=$ [`ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField ((q*ℓ)^2*M') (ModularCurve.FullLevel.levelH (q*ℓ) M'))`](def/ModularCurve_LaurentCoeff.html#L103): the field generated over $L$ by the coefficientwise images of the $q$-expansion function field of $X_H$ of level $N_0=(q\ell)^2M'$, where $H=$ [`ModularCurve.FullLevel.levelH (q*ℓ) M'`](def/ModularCurve_FullLevelJacobian.html#L22) is the kernel of the reduction $(\mathbb{Z}/N_0)^\times\to(\mathbb{Z}/q\ell)^\times$, i.e. the units congruent to $1$ modulo $q\ell$.
--
--   Let $A$ be a henselian discrete valuation ring which is a domain with fraction field $L$ and algebraically closed residue field $\kappa=$ `ResidueField A`, with $q\in\mathfrak m_A$ (`hAq`) and $\xi$ in the image of $A\to L$ (`hξA`), and let $K$ be an $A$-algebra compatibly with $L$. Let $j\in K$ be non-zero whose Laurent expansion is the coefficientwise image of [`ModularCurve.jq`](def/ModularCurve_X0.html#L157), the $q$-expansion $q^{-1}+\dots$ of the modular $j$-invariant (`hj`). Let $\varpi$ generate $\mathfrak m_A$ (`hϖ`), and let $\varpi_t\in A$ satisfy $\varpi_t^{\,q^2-1}=qu$ for some unit $u$ (`hϖt`). Write $C=$ `chartAlgFin A ↥K j` for the $A$-subalgebra of elements of $K$ integral over $A[j]$, and $X=$ [`AlgebraicCurve.TwoChartIntegralModel A ↥K j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) for the scheme obtained by glueing $\mathrm{Spec}\,C$ and the corresponding chart for $j^{-1}$ along the middle chart, with structure morphism `toBase` to $\mathrm{Spec}\,A$. Let $y$ be a maximal ideal of $C$ containing the image of $\varpi$ (`hy`, `hϖy`), such that (`hss`) for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi\colon C\to\Omega$ with kernel $y$ the element $\varphi(j)$ lies in [`ModularCurve.ssJSet q Ω`](def/ModularCurve_SupersingularModuli.html#L7), the set of those $j_0\in\Omega$ such that every elliptic curve over $\Omega$ with $j$-invariant $j_0$ has no non-zero $q$-torsion point.
--
--   Throughout, for $\gamma\in \mathrm{SL}_2(\mathbb{Z})$ a *level automorphism at $\gamma^{-1}$* means an $L$-algebra automorphism $\tau$ of $K$ with [`ModularCurve.FullLevel.IsLevelAutAt L (q*ℓ) ξ (q*ℓ) ((q*ℓ)^2*M') (ModularCurve.FullLevel.levelH (q*ℓ) M') γ⁻¹ K τ`](def/ModularCurve_FullLevelLevelAutAt.html#L29): for every weight $k$, every pair $f,g$ of modular forms on the congruence subgroup attached to $H$ in level $N_0$ with integral $q$-expansions $p_f,p_g$ and $p_g\neq 0$, every $x\in K$ whose Laurent expansion is the embedded quotient of $p_f$ by $p_g$, and every embedding $\iota$ as in `hι`, the $\iota$-image of the expansion of $\tau x$ multiplied by the $q$-expansion of $g\mid_k$`conjElemN (q*ℓ) γ⁻¹` equals the $q$-expansion of $f\mid_k$`conjElemN (q*ℓ) γ⁻¹`.
--
--   **The rigid chart package `hArig`** (summarised here) asserts: for every point $z$ of $X$ such that the germ at $z$ of the pullback of $\varpi$ from $\mathrm{Spec}\,A$ lies in the maximal ideal of $\mathcal O_{X,z}$, and every point $y'$ of $\mathrm{Spec}\,C$ mapping to $z$ and satisfying the supersingularity condition `hss'` (the analogue of `hss` for $y'$), there exist a complete discrete valuation domain $W$, a homomorphism $\sigma\colon A\to W$ with $\mathfrak m_W=(\sigma\varpi)$, power series $f,u,v\in W[[X_0,X_1]]$ with $u,v$ units and $f-$[`DrinfeldCurve.LocalChart.drinfeldForm q W`](def/DrinfeldCurve_LocalChart.html#L18)$\;=f-(X_0X_1^q-X_0^qX_1)\in(X_0,X_1)^{q+2}$, and an isomorphism $e$ of the adic completion of $\mathcal O_{X,z}$ with $S=W[[X_0,X_1]]/(C(\sigma(\varpi_t^{\,q+1}))v-fu)$, for which (writing `toC` for the completion map, `mkS` for the quotient map and `germY` for the canonical map $C\to\mathcal O_{X,z}$ through the chart $\mathrm{Spec}\,C$): (i) $e$ carries the germ of each $a\in A$ to the class of $C(\sigma a)$; (ii) every level automorphism at $\gamma^{-1}$ with $\gamma\in\Gamma_0(M')$ maps $C$ into $C$; (iii) for $\gamma\in\Gamma_0(M')\cap\Gamma(\ell)$ such a $\tau$ fixes $y'$, i.e. $\tau a-a\in y'$ for all $a\in C$; (iv) for $\gamma\in\Gamma_0(M')$, every level automorphism $\tau$ at $\gamma^{-1}$ preserving $C$ and fixing $y'$ in that sense admits $\theta\in\mathrm{Aut}(S)$, $c\in W$ and $M\in M_2(W)$ with $\theta\circ e\circ$`toC`$\circ$`germY`$\;=e\circ$`toC`$\circ$`germY`$\circ\tau$ on $C$, with $\theta$ fixing all constants $C(w)$, with $\theta(X_j)\equiv\sum_i C(M_{ij})X_i$ modulo the square of the ideal generated by the classes of $X_0,X_1$, with $c^{q+1}\equiv1$ and $M_{ij}\equiv c\,\gamma_{ij}$ modulo $\mathfrak m_W$, with $c\equiv1$ whenever $\gamma\in\Gamma(\ell)$, and with $c\not\equiv1$ whenever $\gamma\in\Gamma(q)$ and $\tau\neq\mathrm{id}$; (v) a separation clause: for integers $a_1,b_1,a_2,b_2$ and primes $P_1,P_2$ of $S$, each not containing both classes of $X_0,X_1$, each containing the class of $C(\sigma\varpi)$ and each containing some $a_iX_0+b_iX_1+h_i$ with $h_i\in(X_0,X_1)^2$, if $q\nmid a_1b_2-a_2b_1$ then the contractions of $P_1,P_2$ to $\mathcal O_{X,z}$ differ; (vi) for a prime $P$ of $S$ not containing both classes of $X_0,X_1$, containing the class of $C(\sigma\varpi)$ and containing the class of $X_0+h$ with $h\in(X_0,X_1)^2$, an element $a\in C$ has its image in the contraction of $P$ if and only if every Laurent coefficient of $a$ is the image of an element of $\mathfrak m_A$; (vii) a Drinfeld-chart witness: [`ModularCurve.jqNModC L (q*ℓ)`](def/ModularCurve_JqCoeff.html#L18), the $(q\ell)$-rescaled $q$-expansion of the $j$-invariant, lies in $K$ and in $C$, there are $a_0\in A$ with $j_{q\ell}-a_0\in y'$, an integer $e_0\ge1$ and $h\in(X_0,X_1)^{e_0}$ whose degree-$e_0$ form $\sum_{i\le e_0}(\text{coeff of }X_0^iX_1^{e_0-i}\text{ in }h)\,a^ib^{e_0-i}$ is a unit of $W$ for all $a,b\in W$ not both in $\mathfrak m_W$ with $a^qb-ab^q\in\mathfrak m_W$, and $e$ carries the image of $j_{q\ell}-a_0$ to the class of $h$.
--
--   **The tame-inertia rider `hArigI`** asserts: for $z$, $y'$ as above and for any chart data $W,\sigma,f,u,v,e$ as above satisfying clause (i) and clause (iv), and for every $d\in(\mathbb{Z}/q)^\times$, every pair of ring automorphisms $\sigma_L$ of $L$ and $\sigma_A$ of $A$ compatible under $A\to L$ with $\sigma_A a\equiv a$ modulo $\mathfrak m_A$ for all $a$, every $\pi\in A$ with $\pi^{q^2-1}=q$, every $\tilde\alpha$ with $\sigma_A\pi=\tilde\alpha\pi$ and $\tilde\alpha^{q+1}\equiv d$ modulo $\mathfrak m_A$, and every ring automorphism $\tau$ of $K$ acting on Laurent expansions coefficientwise by $\sigma_L$: $\tau$ maps $C$ into $C$, and for every such preservation, $\tau a-a\in y'$ for all $a\in C$ and there exist $\theta\in\mathrm{Aut}(S)$, $\sigma_W\in\mathrm{Aut}(W)$, $\tilde c\in W$ and $M\in M_2(W)$ with $\theta$ intertwining $\tau$ as in (iv), $\sigma_W\circ\sigma=\sigma\circ\sigma_A$, $\sigma_W w\equiv w$ modulo $\mathfrak m_W$, $\theta(C(w))=C(\sigma_W w)$, $\theta(X_j)\equiv\sum_i C(M_{ij})X_i$ modulo the square of the ideal generated by the classes of $X_0,X_1$, $\tilde c\equiv\sigma(\tilde\alpha^{q+1})$ and $M_{ij}\equiv\tilde c\cdot(\,$[`ModularCurve.FullLevel.diagOneElem q (d^q)⁻¹`](def/ModularCurve_FullLevelJacobian.html#L233)$\,)_{ij}$ modulo $\mathfrak m_W$, where `diagOneElem q` $e$ is $\mathrm{diag}(1,e)$ in $\mathrm{GL}_2(\mathbb{Z}/q)$.
--
--   **One opened chart.** Fix a point $z$, a germ $\varpi_z$ of $\varpi$ lying in the maximal ideal of $\mathcal O_{X,z}$, a point $y'$ of $\mathrm{Spec}\,C$ over $z$ with the supersingularity rider `hss'`, and assume $y'=y$ (`hy'y`). Fix furthermore a complete discrete valuation domain $W_1$, a homomorphism $\sigma_1\colon A\to W_1$ with $\mathfrak m_{W_1}=(\sigma_1\varpi)$, series $f_1,u_1,v_1$ with $u_1,v_1$ units and $f_1$ congruent to `drinfeldForm q W₁` modulo $(X_0,X_1)^{q+2}$, and an isomorphism $e_1$ of the adic completion of $\mathcal O_{X,z}$ with $S=W_1[[X_0,X_1]]/(C(\sigma_1(\varpi_t^{\,q+1}))v_1-f_1u_1)$; the hypothesis `hW₁` is exactly the conjunction of clauses (i)–(vii) above for this chart.
--
--   **The blow-up chart.** Let $J$ be the ideal of $C$ given by `hJ` as the infimum, over all $\gamma\in\Gamma(q)\cap\Gamma_0(M')$ and all level automorphisms $\tau$ at $\gamma^{-1}$ preserving $C$, of the contraction along $\tau|_C$ of the contraction along $e_1\circ$`toC`$\circ$`germY` of the ideal of $S$ generated by the classes of $C(\sigma_1\varpi_t)$, $X_0$ and $X_1$. Let $B$ be the $A$-subalgebra of $K$ given by `hB` as $C$ adjoined with all $x\in K$ such that $x\varpi_t=i$ for some $i\in J$, i.e. the weighted blow-up chart $C[J/\varpi_t]$. Let $\tilde W$ be a valuation subring of $K$ containing $B$ (`hBW`). The hypotheses on $(B,\tilde W)$ are: `hR1`, that $C\subseteq B$ and every element of $K$ is a quotient of two elements of $B$ with non-zero denominator; `hR2`, that $B$ is formally smooth and of finite presentation over $A$ and $B/\varpi B$ has Krull dimension at most $1$; `hR3` (five clauses), that an element of $L$ lies in $\tilde W$ precisely when it comes from $A$, that $\mathfrak m_{\tilde W}$ is generated by $\varpi$, that $\tilde W$ is a discrete valuation ring, that for $b\in C$ one has $b\in y$ if and only if $b\in\mathfrak m_{\tilde W}$, and that $f\in K$ lies in $\tilde W$ precisely when $f=g/h$ with $g,h\in B$ and $h\notin\mathfrak m_{\tilde W}$.
--
--   **The decomposition block `hEQ`** has five clauses. (a) For every $\mathbb{F}_{q^2}$-algebra structure on $\kappa$ there is a surjective ring homomorphism $\rho\colon B\to$ [`DrinfeldCurve.CoordRing q κ`](def/DrinfeldCurve_CoordRing.html#L21), the quotient of $\kappa[x_0,x_1]$ by the principal ideal generated by `drinfeldPoly q κ` $-1$, with $\rho b=0$ exactly for $b\in\mathfrak m_{\tilde W}$, with $\rho(a)$ the image of the residue of $a$ for $a\in A$, and such that for $\gamma\in\Gamma_0(M')$ and every level automorphism $\tau$ at $\gamma^{-1}$ with $f\in\tilde W\iff\tau f\in\tilde W$ there are $c\in\mathbb{F}_{q^2}^\times$ with $($[`ModularCurve.FullLevel.redQ q γ`](def/ModularCurve_FullLevelJacobian.html#L230)$,c)$ in [`DrinfeldCurve.hSubgroup q`](def/DrinfeldCurve_CoordRing.html#L276) (the kernel of $(g,c)\mapsto\det(g)\,c^{q+1}$) satisfying $\rho(\tau b)=$ [`DrinfeldCurve.hAction q κ`](def/DrinfeldCurve_CoordRing.html#L325) applied to that pair, evaluated at $\rho b$, for all $b\in B$ with $\tau b\in B$, together with $c\neq1$ whenever $\gamma\in\Gamma(q)$ and $\tau\neq\mathrm{id}$. (b) Level automorphisms at $\gamma^{-1}$ with $\gamma\in\Gamma_0(M')$ map $B$ into $B$. (c) Every prime $Q$ of $B$ containing $\varpi$ is reached: there are $\gamma\in\Gamma(q)\cap\Gamma_0(M')$ and a level automorphism $\tau$ at $\gamma^{-1}$ such that every $b\in B$ lying in $\mathfrak m_{\tilde W}$ has $\tau b\in B$ and $\tau b\in Q$. (d) If $b\in B$ satisfies $\tau b\in\mathfrak m_{\tilde W}$ for all $\gamma\in\Gamma(q)\cap\Gamma_0(M')$ and all level automorphisms $\tau$ at $\gamma^{-1}$ with $\tau b\in B$, then $\varpi\mid b$ in $B$. (e) A level automorphism at $\gamma^{-1}$ with $\gamma\in\Gamma_0(M')$ which preserves $y$ on the chart (for $b\in C$ with $\tau b\in C$: $b\in y\iff\tau b\in y$) preserves $\tilde W$.
--
--   **Conclusion.** For every $\mathbb{F}_{q^2}$-algebra structure on $\kappa$ there exists a ring homomorphism $\rho\colon B\to$ [`DrinfeldCurve.CoordRing q κ`](def/DrinfeldCurve_CoordRing.html#L21) such that:
--
--   1. $\rho$ is surjective;
--
--   2. for $b\in B$, $\rho b=0$ if and only if $b\in\mathfrak m_{\tilde W}$;
--
--   3. for $a\in A$, $\rho(a)$ is the image of the residue class of $a$ under $\kappa\to$ `CoordRing q κ`;
--
--   4. for every $\gamma\in\Gamma_0(M')$ and every level automorphism $\tau$ at $\gamma^{-1}$ satisfying $f\in\tilde W\iff\tau f\in\tilde W$, there is $c\in\mathbb{F}_{q^2}^\times$ with $($`redQ q γ`$,c)\in$ `hSubgroup q` such that $\rho(\tau b)=$ `hAction q κ` of that pair applied to $\rho b$ for all $b\in B$ with $\tau b\in B$; moreover $c\neq1$ whenever $\gamma\in\Gamma(q)$ and $\tau$ is not the identity; and moreover the scalar $c$ is realised on its own: there exist $\gamma'\in\Gamma(q)\cap\Gamma_0(M')$ and a level automorphism $\tau'$ at $\gamma'^{-1}$ with $f\in\tilde W\iff\tau' f\in\tilde W$, and $(1,c)\in$ `hSubgroup q`, such that $\rho(\tau' b)=$ `hAction q κ` of $(1,c)$ applied to $\rho b$ for all $b\in B$ with $\tau' b\in B$;
--
--   5. (inertia) for every $\pi\in A$ with $\pi^{q^2-1}=q$, every pair of ring automorphisms $\sigma_L$ of $L$ and $\sigma_A$ of $A$ compatible under $A\to L$ with $\sigma_A a-a\in\mathfrak m_A$ for all $a\in A$, every $\tilde\alpha\in A$ with $\sigma_A\pi=\tilde\alpha\pi$, every $\alpha\in\mathbb{F}_{q^2}^\times$ whose image in $\kappa$ is the residue of $\tilde\alpha$, and every ring automorphism $\tau$ of $K$ acting on Laurent expansions coefficientwise by $\sigma_L$: $\tau$ maps $B$ into $B$, $f\in\tilde W\iff\tau f\in\tilde W$, and for every $d\in(\mathbb{Z}/q)^\times$ whose image in $\mathbb{F}_{q^2}$ equals $\alpha^{q+1}$, every proof that $($`diagOneElem q (d^q)⁻¹`$,\alpha^q)\in$ `hSubgroup q`, and every $b\in B$ with $\tau b\in B$, one has $\rho(\tau b)=$ `hAction q κ` of $(\mathrm{diag}(1,(d^q)^{-1}),\alpha^q)$ applied to $\rho b$.
--
--   Thus the conclusion is the first clause of `hEQ` augmented by the linked-scalar existential in 4 and by the inertia clause 5.
--
--   This is the inertia companion to the level-equivariance statement for the exceptional Drinfeld curve arising as the special fibre of the weighted blow-up chart $B=C[J/\varpi_t]$ at a supersingular point of the integral model of the modular curve of level $(q\ell)^2M'$: it identifies the reduction $B\to\kappa[x_0,x_1]/(\text{drinfeldPoly}-1)$ together with the action on it of both the level automorphisms and of the tame inertia of $A$, the latter acting through the pair $(\mathrm{diag}(1,d^{-q}),\alpha^q)$ in the group [`DrinfeldCurve.hSubgroup q`](def/DrinfeldCurve_CoordRing.html#L276). It is used by [`ModularCurve.FullLevel.AuxLevel.exists_supersingularAffineChart_ends_moduliHasse_commonChart_orbitPoles_inertia_chartAlgFin_of_stalk_drinfeldChart_moduliHasse_igusaSep_deckSep_linkedScalars_linkedInertia`](thm.html#ModularCurve.FullLevel.AuxLevel.exists_supersingularAffineChart_ends_moduliHasse_commonChart_orbitPoles_inertia_chartAlgFin_of_stalk_drinfeldChart_moduliHasse_igusaSep_deckSep_linkedScalars_linkedInertia), which assembles the supersingular affine chart with its Hasse-invariant and separation data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevel_blowupChart_drinfeldFibre_levelAut_linkedScalars_inertia_of_decomposition_of_eq_adjoin_of_drinfeldChartWitness_of_stalk_drinfeldChart_inertia.lean

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

theorem ModularCurve.FullLevel.AuxLevel.blowupChart_drinfeldFibre_levelAut_linkedScalars_inertia_of_decomposition_of_eq_adjoin_of_drinfeldChartWitness_of_stalk_drinfeldChart_inertia
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

    (hArigI :
    ∀ (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j))
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

    (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
    (_ : IsAdicComplete (IsLocalRing.maximalIdeal W) W) (σ : A →+* W)
    (hσϖ : IsLocalRing.maximalIdeal W = Ideal.span {σ ϖ})
    (f u v : MvPowerSeries (Fin 2) W) (hu : IsUnit u) (hv : IsUnit v)
    (hf : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
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
        Ideal.Quotient.mk _ (MvPowerSeries.C (σ a))) →

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

                (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥K, τ k = k) → c - 1 ∉ IsLocalRing.maximalIdeal W)) →

    ∀ (d : (ZMod q)ˣ) (σL : L ≃+* L) (σA : A ≃+* A),
      (∀ a : A, algebraMap A L (σA a) = σL (algebraMap A L a)) →

      (∀ a : A, σA a - a ∈ IsLocalRing.maximalIdeal A) →

      ∀ (π : A), π ^ (q ^ 2 - 1) = (q : A) → ∀ (αt : A), σA π = αt * π →
      αt ^ (q + 1) - (((d : ZMod q).val : ℕ) : A) ∈ IsLocalRing.maximalIdeal A →
      ∀ τ : ↥K ≃+* ↥K,

        (∀ x : ↥K, ((τ x : ↥K) : LaurentSeries L) = ModularCurve.coeffMap σL.toRingHom ((x : ↥K) : LaurentSeries L)) →

        (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
          τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) ∧
        ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
            τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),

          (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
            (((τ.toRingHom.restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
              (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y'.asIdeal)) ∧

          ∃ (θ : S ≃+* S) (σW : W ≃+* W) (ct : W) (M : Matrix (Fin 2) (Fin 2) W),
            (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
              θ (e (toC (germY a))) = e (toC (germY ((τ.toRingHom.restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
              (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a)))) ∧
            (∀ a : A, σW (σ a) = σ (σA a)) ∧
            (∀ w : W, σW w - w ∈ IsLocalRing.maximalIdeal W) ∧
            (∀ w : W, θ (mkS (MvPowerSeries.C w)) = mkS (MvPowerSeries.C (σW w))) ∧
            (∀ jj : Fin 2, θ (mkS (MvPowerSeries.X jj)) -
                mkS (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) ∈
              (Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2) ∧

            (ct - σ (αt ^ (q + 1)) ∈ IsLocalRing.maximalIdeal W) ∧
            (∀ ii jj : Fin 2, M ii jj -
                ct * (((((ModularCurve.FullLevel.diagOneElem q (d ^ q)⁻¹ : CuspidalType.GL2 q) :
                    Matrix (Fin 2) (Fin 2) (ZMod q)) ii jj).val : ℕ) : W) ∈ IsLocalRing.maximalIdeal W))

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
          ∀ f : ↥K, f ∈ W ↔ τ f ∈ W)) :

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
                (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥K, τ k = k) → c ≠ 1) ∧

                (∃ (γ' : SL(2, ℤ)) (_ : γ' ∈ CongruenceSubgroup.Gamma q) (_ : γ' ∈ CongruenceSubgroup.Gamma0 M') (τ' : ↥K ≃ₐ[L] ↥K)
                    (_ : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') γ'⁻¹ K τ') (_ : ∀ f : ↥K, f ∈ W ↔ τ' f ∈ W)
                    (hmem' : ((1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)), c) ∈ DrinfeldCurve.hSubgroup q),
                  ∀ (b : ↥B) (hb : τ' (b : ↥K) ∈ B), ρ ⟨τ' (b : ↥K), hb⟩ = DrinfeldCurve.hAction q (ResidueField A) ⟨_, hmem'⟩ (ρ b))) ∧

          (∀ (π : A), π ^ (q ^ 2 - 1) = (q : A) →
            ∀ (σL : L ≃+* L) (σA : A ≃+* A), (∀ a : A, algebraMap A L (σA a) = σL (algebraMap A L a)) →
              (∀ a : A, σA a - a ∈ maximalIdeal A) →
              ∀ (αt : A), σA π = αt * π →
              ∀ (α : (GaloisField q 2)ˣ), algebraMap (GaloisField q 2) (ResidueField A) (α : GaloisField q 2) = residue A αt →
              ∀ τ : ↥K ≃+* ↥K,
                (∀ x : ↥K, ((τ x : ↥K) : LaurentSeries L) = ModularCurve.coeffMap σL.toRingHom ((x : ↥K) : LaurentSeries L)) →
                (∀ f : ↥K, f ∈ B → τ f ∈ B) ∧ (∀ f : ↥K, f ∈ W ↔ τ f ∈ W) ∧
                ∀ (d : (ZMod q)ˣ), algebraMap (ZMod q) (GaloisField q 2) (d : ZMod q) = (α : GaloisField q 2) ^ (q + 1) →
                  ∀ (hmem : (ModularCurve.FullLevel.diagOneElem q (d ^ q)⁻¹, α ^ q) ∈ DrinfeldCurve.hSubgroup q)
                    (b : ↥B) (hb : τ (b : ↥K) ∈ B),
                    ρ ⟨τ (b : ↥K), hb⟩ = DrinfeldCurve.hAction q (ResidueField A) ⟨_, hmem⟩ (ρ b))) := by sorry
