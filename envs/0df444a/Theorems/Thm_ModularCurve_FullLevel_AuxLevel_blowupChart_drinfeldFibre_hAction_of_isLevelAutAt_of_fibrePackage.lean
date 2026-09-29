-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevel_blowupChart_drinfeldFibre_hAction_of_isLevelAutAt_of_fibrePackage
-- name    : ModularCurve.FullLevel.AuxLevel.blowupChart_drinfeldFibre_hAction_of_isLevelAutAt_of_fibrePackage
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:14.444979+00:00
-- url     : https://prove2.me/theorems/aa176975-a006-5033-9d87-ca14aeb63950
-- title:
--   Level automorphisms act on the Drinfeld fibre through H
-- statement:
--   Throughout, $q$ is a prime with $5\le q$, $M'$ a nonzero natural number with $q\nmid M'$, and $\ell$ a prime with $3\le\ell$, $\ell\ne q$ and $\ell\nmid M'$; $L$ is a field of characteristic zero and $\xi\in L$ a primitive $(q\ell)$-th root of unity, and the hypothesis `hι` provides a ring homomorphism $\iota:L\to\mathbb C$ with $\iota\xi=\exp(2\pi i/(q\ell))$. Further, $K$ is an intermediate field of $L\subseteq L((t))$, and `hK` requires $K=$ [`ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField ((q*ℓ)^2*M') (ModularCurve.FullLevel.levelH (q*ℓ) M'))`](def/ModularCurve_LaurentCoeff.html#L103), that is, the subfield of $L((t))$ generated over $L$ by the coefficientwise image under [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81) of the field of $q$-expansions over $\mathbb Q$ attached to the subgroup [`CohCarrier.GammaH ((q*ℓ)^2*M') H`](def/CohCarrier_Level.html#L133) of $\mathrm{SL}_2(\mathbb Z)$, where $H=$ [`ModularCurve.FullLevel.levelH (q*ℓ) M'`](def/ModularCurve_FullLevelJacobian.html#L22) is the kernel of the reduction map $(\mathbb Z/(q\ell)^2M')^\times\to(\mathbb Z/q\ell)^\times$, i.e. the units congruent to $1$ modulo $q\ell$.
--
--   For $\gamma\in\mathrm{SL}_2(\mathbb Z)$ and $\tau$ an $L$-algebra automorphism of $K$, the phrase '$\tau$ is a level automorphism at $\gamma^{-1}$' abbreviates [`ModularCurve.FullLevel.IsLevelAutAt L (q*ℓ) ξ (q*ℓ) ((q*ℓ)^2*M') (ModularCurve.FullLevel.levelH (q*ℓ) M') γ⁻¹ K τ`](def/ModularCurve_FullLevelLevelAutAt.html#L29), which unfolds to the following condition: for every weight $k\in\mathbb Z$, every pair $f,g$ of modular forms of weight $k$ for [`CohCarrier.GammaH ((q*ℓ)^2*M') H`](def/CohCarrier_Level.html#L133) viewed in $\mathrm{GL}_2(\mathbb R)$, every pair of integral power series $p_f,p_g$ which are the $q$-expansions of $f$ and of $g$ in the sense of [`ModularCurve.IsIntegralQExp`](def/ModularCurve_X1.html#L37), with `intSeriesC ℚ pg ≠ 0`, every $x\in K$ whose Laurent expansion equals the coefficientwise image of `intSeriesC ℚ pf / intSeriesC ℚ pg`, and every ring homomorphism $\iota:L\to\mathbb C$ with $\iota\xi=\exp(2\pi i/(q\ell))$, the identity
--   $$\mathrm{coeffMap}\,\iota\,(\tau x)\cdot\big(\text{$q$-expansion of } g\mid_k\delta\big)=\text{$q$-expansion of } f\mid_k\delta,\qquad \delta=\mathrm{conjElemN}\,(q\ell)\,\gamma^{-1},$$
--   holds, where for $m$ and $\beta$ the matrix `conjElemN m β` has rows $(\beta_{00},\beta_{01}/m)$ and $(m\beta_{10},\beta_{11})$.
--
--   Base data. $A$ is a discrete valuation domain with an $L$-algebra structure making $L$ its fraction field, Henselian local with algebraically closed residue field; $q\in\mathfrak m_A$ (`hAq`) and $\xi$ lies in the image of $A$ (`hξA`); $K$ carries a compatible $A$-algebra structure. The element $j\in K$ has Laurent expansion [`ModularCurve.coeffEmb L ModularCurve.jq`](def/ModularCurve_LaurentCoeff.html#L81), the $q$-expansion of the modular $j$-function, and $j\ne0$. Also $\varpi$ generates $\mathfrak m_A$ (`hϖ`), and $\varpi_t\in A$ satisfies $\varpi_t^{\,q^2-1}=qu$ for some unit $u$ (`hϖt`).
--
--   Chart and supersingular point. Write $C=$ `chartAlgFin A K j`, the $A$-subalgebra of $K$ consisting of the elements integral over $A[j]$. Then $y$ is an ideal of $C$, maximal (`hy`), containing the image of $\varpi$ (`hϖy`), and `hss` requires: for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi:C\to\Omega$ with kernel $y$, the element $\varphi(\mathrm{jChartFin})$, i.e. the image of $j$, lies in [`ModularCurve.ssJSet q Ω`](def/ModularCurve_SupersingularModuli.html#L7), the set of those $j_0\in\Omega$ for which every elliptic curve over $\Omega$ with $j$-invariant $j_0$ has no nonzero affine point killed by $q$.
--
--   Integral model. $X=$ [`AlgebraicCurve.TwoChartIntegralModel A K j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) is the pushout of the two affine charts $\mathrm{Spec}\,C$ and $\mathrm{Spec}$ of the integral closure of $A[j^{-1}]$ along the middle chart, with structure morphism `toBase` to $\mathrm{Spec}\,A$. A point $z$ of $X$ is given, together with the element $\varpi_z$ of the stalk at $z$ defined (`hϖz`) as the germ at $z$ of the global section of $X$ obtained from $\varpi$ along `toBase`, and `hz` requires $\varpi_z$ to lie in the maximal ideal of that stalk. Moreover $y'$ is a point of `XFin A K j` $=\mathrm{Spec}\,C$ with `ιFin` mapping $y'$ to $z$ (`hy'`), satisfying the same supersingularity condition for its prime ideal (`hss'`), and `hy'y` requires $y'.\mathrm{asIdeal}=y$.
--
--   Formal Drinfeld model. $W_1$ is a discrete valuation domain, adically complete for its maximal ideal, $\sigma_1:A\to W_1$ a ring homomorphism with $\mathfrak m_{W_1}=(\sigma_1\varpi)$ (`hσ₁`); $f_1,u_1,v_1\in W_1[[X_0,X_1]]$ with $u_1,v_1$ units and $f_1-(X_0X_1^q-X_0^qX_1)\in(X_0,X_1)^{q+2}$ (`hf₁`, the second term being [`DrinfeldCurve.LocalChart.drinfeldForm q W₁`](def/DrinfeldCurve_LocalChart.html#L18)); and $e_1$ is a ring isomorphism from the adic completion of the stalk $\mathcal O_{X,z}$ with respect to its maximal ideal onto
--   $$S=W_1[[X_0,X_1]]\big/\big(C(\sigma_1(\varpi_t^{q+1}))\,v_1-f_1u_1\big).$$
--   Below, `toC` denotes the completion map from the stalk `STK` to `CMP`, `mkS` the quotient map onto $S$, `germY` the canonical ring homomorphism $C\to$ `STK` sending a chart function to its germ at $z$ through the open immersion `ιFin`, and $\Psi$ the composite $e_1\circ\mathrm{toC}\circ\mathrm{germY}:C\to S$.
--
--   The hypothesis `hW₁` is a conjunction of seven clauses: (1) for every $a\in A$, $e_1$ carries the image in `CMP` of the germ at $z$ of $a$ (along `toBase`) to $\mathrm{mkS}(C(\sigma_1 a))$; (2) for every $\gamma\in\Gamma_0(M')$ and every level automorphism $\tau$ at $\gamma^{-1}$, $\tau$ maps $C$ into $C$; (3) for every $\gamma\in\Gamma_0(M')\cap\Gamma(\ell)$, every level automorphism $\tau$ at $\gamma^{-1}$ and every proof that $\tau$ preserves $C$, the induced endomorphism of $C$ satisfies $\tau(a)-a\in y'.\mathrm{asIdeal}$ for all $a\in C$; (4) for every $\gamma\in\Gamma_0(M')$, every level automorphism $\tau$ at $\gamma^{-1}$ preserving $C$ and inducing the identity modulo $y'.\mathrm{asIdeal}$, there are a ring automorphism $\theta$ of $S$, an element $c\in W_1$ and a matrix $M\in \mathrm{Mat}_2(W_1)$ such that $\theta\circ\Psi=\Psi\circ\tau$ on $C$, $\theta$ fixes every $\mathrm{mkS}(C(w))$, $\theta(\mathrm{mkS}(X_j))-\mathrm{mkS}(\sum_i C(M_{ij})X_i)$ lies in the square of the ideal generated by $\mathrm{mkS}(X_0),\mathrm{mkS}(X_1)$ for each $j$, $c^{q+1}-1\in\mathfrak m_{W_1}$, $M_{ij}-c\,\gamma_{ij}\in\mathfrak m_{W_1}$ for all $i,j$, $c-1\in\mathfrak m_{W_1}$ whenever $\gamma\in\Gamma(\ell)$, and $c-1\notin\mathfrak m_{W_1}$ whenever $\gamma\in\Gamma(q)$ and $\tau$ is not the identity; (5) for all integers $a_1,b_1,a_2,b_2$ and all primes $P_1,P_2$ of $S$, each omitting at least one of $\mathrm{mkS}(X_0),\mathrm{mkS}(X_1)$, each containing $\mathrm{mkS}(C(\sigma_1\varpi))$, and each containing an element $\mathrm{mkS}(C(a_i)X_0+C(b_i)X_1+h)$ with $h\in(X_0,X_1)^2$, if $q\nmid a_1b_2-a_2b_1$ then the contractions of $P_1$ and $P_2$ along $e_1\circ\mathrm{toC}$ are distinct; (6) for every prime $P$ of $S$ omitting at least one of $\mathrm{mkS}(X_0),\mathrm{mkS}(X_1)$, containing $\mathrm{mkS}(C(\sigma_1\varpi))$ and containing some $\mathrm{mkS}(C(1)X_0+C(0)X_1+h)$ with $h\in(X_0,X_1)^2$, and for every $a\in C$: the germ of $a$ lies in the contraction of $P$ along $e_1$ if and only if every Laurent coefficient of $a$ lies in the image of $\mathfrak m_A$; (7) the series [`ModularCurve.jqNModC L (q*ℓ)`](def/ModularCurve_JqCoeff.html#L18), the image of the $j$-expansion under the substitution $t\mapsto t^{q\ell}$, lies in $K$ and in $C$, and there are $a_0\in A$ with the corresponding element of $C$ congruent to $a_0$ modulo $y'.\mathrm{asIdeal}$, an integer $e_0\ge1$ and $h\in(X_0,X_1)^{e_0}$ such that for all $a,b\in W_1$ with $a$ or $b$ a unit and $a^qb-ab^q\in\mathfrak m_{W_1}$ the sum $\sum_{i=0}^{e_0}(\text{coefficient of }X_0^iX_1^{e_0-i}\text{ in }h)\,a^ib^{e_0-i}$ is a unit, and such that $\Psi$ applied to that element minus $a_0$ equals $\mathrm{mkS}(h)$.
--
--   Blow-up ideal and algebra. $J$ is an ideal of $C$, and `hJ` requires $J$ to be the infimum of the ideals $\tau^{-1}\big(\Psi^{-1}(\mathrm{span}\{\mathrm{mkS}(C(\sigma_1\varpi_t)),\mathrm{mkS}(X_0),\mathrm{mkS}(X_1)\})\big)$, taken over all $\gamma\in\Gamma(q)\cap\Gamma_0(M')$ and all level automorphisms $\tau$ at $\gamma^{-1}$ preserving $C$. The subalgebra $B$ of $K$ over $A$ is required (`hB`) to be the $A$-algebra underlying the $C$-algebra generated by $\{x\in K:\exists\,i\in J,\ x\varpi_t=i\}$, and `hCB` requires $C\le B$.
--
--   The hypothesis `hK1` has three clauses: (a) for $\gamma\in\Gamma_0(M')$ and a level automorphism $\tau$ at $\gamma^{-1}$ preserving $C$ and inducing the identity modulo $y$, and for every $a\in C$, $\Psi(a)$ lies in $\mathrm{span}\{\mathrm{mkS}(C(\sigma_1\varpi_t)),\mathrm{mkS}(X_0),\mathrm{mkS}(X_1)\}$ if and only if $\Psi(\tau a)$ does; (b) for $\gamma\in\Gamma_0(M')$ and a level automorphism $\tau$ at $\gamma^{-1}$, and for $a\in C$ with $\tau a\in C$, one has $a\in J$ if and only if $\tau a\in J$; (c) for $\gamma\in\Gamma_0(M')$ and a level automorphism $\tau$ at $\gamma^{-1}$, $\tau$ maps $B$ into $B$.
--
--   The hypothesis `hbridge` has eight clauses: $\Psi^{-1}(\mathrm{span}\{\mathrm{mkS}(C(\sigma_1\varpi)),\mathrm{mkS}(X_0),\mathrm{mkS}(X_1)\})=y$; for every $n$ and every $s\in S$ there is $a\in C$ with $\Psi(a)-s$ in the $n$-th power of that ideal; $\Psi(a)=\mathrm{mkS}(C(\sigma_1a))$ for $a\in A$; every element of $C$ is congruent modulo $y$ to an element of $A$; every element of $W_1$ is congruent modulo $\mathfrak m_{W_1}$ to an element of $\sigma_1(A)$; $\sigma_1^{-1}(\mathfrak m_{W_1})=\mathfrak m_A$; the ideal $\mathrm{span}\{\mathrm{mkS}(C(\sigma_1\varpi)),\mathrm{mkS}(X_0),\mathrm{mkS}(X_1)\}$ is maximal and is the only maximal ideal of $S$; and $S$ is flat as a $C$-module via $\Psi$.
--
--   The hypothesis `hcentre` has four clauses: the ideal of $S$ generated by $\Psi(J)$ equals $\mathrm{span}\{\mathrm{mkS}(C(\sigma_1\varpi_t)),\mathrm{mkS}(X_0),\mathrm{mkS}(X_1)\}$; there is an ideal $I$ of $C$ with $J=\Psi^{-1}(\mathrm{span}\{\mathrm{mkS}(C(\sigma_1\varpi_t)),\mathrm{mkS}(X_0),\mathrm{mkS}(X_1)\})\cap I$ and $I+y=C$; $J\le y$; and the image of $\varpi_t$ lies in $J$. Finally, an algebra structure of the field `GaloisField q 2` $=\mathbb F_{q^2}$ on the residue field $\kappa_A$ of $A$ is given.
--
--   Conclusion. Put $L_{\mathrm{loc}}=$ `Localization.Away (mkS (MvPowerSeries.C (σ₁ ϖt)))` with structure map $\iota_S:S\to L_{\mathrm{loc}}$, and set $x_0=\iota_S(\mathrm{mkS}(X_0))/\mathrm{mkS}(C(\sigma_1\varpi_t))$ and $x_1=\iota_S(\mathrm{mkS}(X_1))/\mathrm{mkS}(C(\sigma_1\varpi_t))$, and let $R_{\mathrm{loc}}$ be the subring of $L_{\mathrm{loc}}$ generated by the image of $\iota_S$ together with $x_0$ and $x_1$. The assertion is then: for every ring homomorphism $\Phi:B\to L_{\mathrm{loc}}$, every proof that the image of $\iota_S$, the elements $x_0,x_1$, and the image of $\Phi$ all lie in $R_{\mathrm{loc}}$, every ring homomorphism $t_W:W_1\to\kappa_A$, every $c_R\in\kappa_A$, and all ring homomorphisms $\rho_R:R_{\mathrm{loc}}\to$ [`DrinfeldCurve.CoordRing q κ_A`](def/DrinfeldCurve_CoordRing.html#L21) and $\rho:B\to$ [`DrinfeldCurve.CoordRing q κ_A`](def/DrinfeldCurve_CoordRing.html#L21) — where `CoordRing q k` is the quotient of $k[X_0,X_1]$ by the ideal generated by [`DrinfeldCurve.drinfeldPoly q k - 1`](def/DrinfeldCurve_CoordRing.html#L17), with $x$ and $y$ the images of $X_0$ and $X_1$ — subject to the seven normalisations: $\Phi$ agrees on $C$ with $\iota_S\circ\Psi$; for $x\in B$ and $i\in J$ with $x\varpi_t=i$ in $K$ one has $\Phi(x)\cdot\iota_S(\mathrm{mkS}(C(\sigma_1\varpi_t)))=\iota_S(\Psi(i))$; $t_W\circ\sigma_1$ is the residue map of $A$ and $t_W$ kills $\mathfrak m_{W_1}$; $c_R\ne0$; $\rho_R(\iota_S(\mathrm{mkS}(F)))$ is the image of $t_W(\text{constant coefficient of }F)$ for every $F\in W_1[[X_0,X_1]]$; $\rho_R(x_0)=c_R\cdot x$ and $\rho_R(x_1)=c_R\cdot y$; and $\rho=\rho_R\circ\Phi$ on $B$ — the following two statements hold.
--
--   First, for every $\gamma\in\Gamma_0(M')$ and every level automorphism $\tau$ at $\gamma^{-1}$ which stabilises $y$, in the sense that for $b\in C$ with $\tau b\in C$ one has $b\in y$ if and only if $\tau b\in y$, there is a unit $c\in\mathbb F_{q^2}^\times$ such that the pair $(\mathrm{redQ}\,q\,\gamma,c)$ lies in [`DrinfeldCurve.hSubgroup q`](def/DrinfeldCurve_CoordRing.html#L276), the kernel of the character sending $(g,c)$ to the product of the image of $\det g$ in $\mathbb F_{q^2}^\times$ with $c^{q+1}$, where `redQ q γ` is the image of $\gamma$ in $\mathrm{GL}_2(\mathbb Z/q)$, and such that: $\rho(\tau b)=$ [`DrinfeldCurve.hAction q κ_A`](def/DrinfeldCurve_CoordRing.html#L325) at $(\mathrm{redQ}\,q\,\gamma,c)$ applied to $\rho(b)$, for all $b\in B$ with $\tau b\in B$; if $\gamma\in\Gamma(q)$ and $\tau$ is not the identity on $K$ then $c\ne1$; and there exist $\gamma'\in\Gamma(q)\cap\Gamma_0(M')$ and a level automorphism $\tau'$ at $\gamma'^{-1}$ stabilising $y$ in the same sense, with $(1,c)\in$ `hSubgroup q`, such that $\rho(\tau'b)=$ `hAction q κ_A` at $(1,c)$ applied to $\rho(b)$ for all $b\in B$ with $\tau'b\in B$.
--
--   Second, there exist $\gamma'\in\Gamma(q)\cap\Gamma_0(M')$ and a level automorphism $\tau'$ at $\gamma'^{-1}$ stabilising $y$ in the same sense, with $(1,-1)\in$ `hSubgroup q`, such that $\rho(\tau'b)=$ `hAction q κ_A` at $(1,-1)$ applied to $\rho(b)$ for all $b\in B$ with $\tau'b\in B$.
--
--   This is the comparison step which transports the action of the level automorphisms of the function field $K$ fixing a supersingular closed point onto the Drinfeld fibre of the blow-up chart, identifying it with the action of the subgroup $H\subseteq\mathrm{GL}_2(\mathbb F_q)\times\mathbb F_{q^2}^\times$ on the Drinfeld coordinate ring over the residue field, with the scalar part faithful on the $\Gamma(q)$-part and with the scalar and the central element $(1,-1)$ both realised by automorphisms attached to elements of $\Gamma(q)\cap\Gamma_0(M')$. It feeds the subsequent decomposition-group and inertia analyses of the same chart.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevel_blowupChart_drinfeldFibre_hAction_of_isLevelAutAt_of_fibrePackage.lean

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

theorem ModularCurve.FullLevel.AuxLevel.blowupChart_drinfeldFibre_hAction_of_isLevelAutAt_of_fibrePackage
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
    (hCB : chartAlgFin A (↥K) j ≤ B)

    (hK1 :
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
            ∀ f : ↥K, f ∈ B → τ f ∈ B))

    (hbridge :
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

        Ideal.comap ((e₁ : CMP →+* S).comp (toC.comp germY)) (Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖ)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) = y ∧

        (∀ (n : ℕ) (s : S), ∃ a : ↥(chartAlgFin A (↥K) j), ((e₁ : CMP →+* S).comp (toC.comp germY)) a - s ∈ (Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖ)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ n) ∧

        (∀ a : A, ((e₁ : CMP →+* S).comp (toC.comp germY)) (algebraMap A ↥(chartAlgFin A (↥K) j) a) = mkS (MvPowerSeries.C (σ₁ a))) ∧

        (∀ c : ↥(chartAlgFin A (↥K) j), ∃ a : A, c - algebraMap A ↥(chartAlgFin A (↥K) j) a ∈ y) ∧
        (∀ w : W₁, ∃ a : A, w - σ₁ a ∈ IsLocalRing.maximalIdeal W₁) ∧
        Ideal.comap σ₁ (IsLocalRing.maximalIdeal W₁) = IsLocalRing.maximalIdeal A ∧

        (Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖ)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}).IsMaximal ∧ (∀ I : Ideal S, I.IsMaximal → I = Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖ)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ∧

        (letI : Algebra ↥(chartAlgFin A (↥K) j) S := (((e₁ : CMP →+* S).comp (toC.comp germY))).toAlgebra
         Module.Flat ↥(chartAlgFin A (↥K) j) S))

    (hcentre :
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

        Ideal.map ((e₁ : CMP →+* S).comp (toC.comp germY)) J = Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖt)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)} ∧

        (∃ I : Ideal ↥(chartAlgFin A (↥K) j),
            J = Ideal.comap ((e₁ : CMP →+* S).comp (toC.comp germY)) (Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖt)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ⊓ I ∧ I ⊔ y = ⊤) ∧
        J ≤ y ∧ algebraMap A ↥(chartAlgFin A (↥K) j) ϖt ∈ J)
    (inst : Algebra (GaloisField q 2) (ResidueField A)) :
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
        let Lloc := Localization.Away (mkS (MvPowerSeries.C (σ₁ ϖt)))
        let ιS : S →+* Lloc := algebraMap S Lloc
        let x₀ : Lloc := ιS (mkS (MvPowerSeries.X 0)) * IsLocalization.Away.invSelf (S := Lloc) (mkS (MvPowerSeries.C (σ₁ ϖt)))
        let x₁ : Lloc := ιS (mkS (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf (S := Lloc) (mkS (MvPowerSeries.C (σ₁ ϖt)))
        let Rloc : Subring Lloc := Subring.closure (Set.range ιS ∪ {x₀, x₁})
        ∀ (Φ : ↥B →+* Lloc) (hιR : ∀ s : S, ιS s ∈ Rloc) (hx₀ : x₀ ∈ Rloc) (hx₁ : x₁ ∈ Rloc) (hΦR : ∀ b : ↥B, Φ b ∈ Rloc)
          (tW : W₁ →+* ResidueField A) (cR : ResidueField A)
          (ρR : ↥Rloc →+* DrinfeldCurve.CoordRing q (ResidueField A))
          (ρ : ↥B →+* DrinfeldCurve.CoordRing q (ResidueField A)),

          (∀ a : ↥(chartAlgFin A (↥K) j), Φ ⟨(a : ↥K), hCB a.2⟩ = ιS (((e₁ : CMP →+* S).comp (toC.comp germY)) a)) →
          (∀ (x : ↥B) (i : ↥(chartAlgFin A (↥K) j)), i ∈ J → (x : ↥K) * algebraMap A ↥K ϖt = (i : ↥K) →
              Φ x * ιS (mkS (MvPowerSeries.C (σ₁ ϖt))) = ιS (((e₁ : CMP →+* S).comp (toC.comp germY)) i)) →
          (∀ a : A, tW (σ₁ a) = residue A a) → (∀ w : W₁, w ∈ IsLocalRing.maximalIdeal W₁ → tW w = 0) →
          cR ≠ 0 →
          (∀ F : MvPowerSeries (Fin 2) W₁, ρR ⟨ιS (mkS F), hιR (mkS F)⟩ =
              algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) (tW (MvPowerSeries.constantCoeff F))) →
          ρR ⟨x₀, hx₀⟩ = algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) cR * DrinfeldCurve.x q (ResidueField A) →
          ρR ⟨x₁, hx₁⟩ = algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) cR * DrinfeldCurve.y q (ResidueField A) →
          (∀ b : ↥B, ρ b = ρR ⟨Φ b, hΦR b⟩) →

          (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
            ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
              (∀ (b : ↥(chartAlgFin A (↥K) j)) (hb : τ (b : ↥K) ∈ chartAlgFin A (↥K) j),
                  b ∈ y ↔ (⟨τ (b : ↥K), hb⟩ : ↥(chartAlgFin A (↥K) j)) ∈ y) →
              ∃ (c : (GaloisField q 2)ˣ) (hmem : (ModularCurve.FullLevel.redQ q γ, c) ∈ DrinfeldCurve.hSubgroup q),
                (∀ (b : ↥B) (hb : τ (b : ↥K) ∈ B), ρ ⟨τ (b : ↥K), hb⟩ = DrinfeldCurve.hAction q (ResidueField A) ⟨_, hmem⟩ (ρ b)) ∧
                (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥K, τ k = k) → c ≠ 1) ∧
                (∃ (γ' : SL(2, ℤ)) (_ : γ' ∈ CongruenceSubgroup.Gamma q) (_ : γ' ∈ CongruenceSubgroup.Gamma0 M') (τ' : ↥K ≃ₐ[L] ↥K)
                   (_ : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') γ'⁻¹ K τ')
                   (_ : (∀ (b : ↥(chartAlgFin A (↥K) j)) (hb : τ' (b : ↥K) ∈ chartAlgFin A (↥K) j),
                  b ∈ y ↔ (⟨τ' (b : ↥K), hb⟩ : ↥(chartAlgFin A (↥K) j)) ∈ y))
                   (hmem' : ((1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)), c) ∈ DrinfeldCurve.hSubgroup q),
                   ∀ (b : ↥B) (hb : τ' (b : ↥K) ∈ B), ρ ⟨τ' (b : ↥K), hb⟩ = DrinfeldCurve.hAction q (ResidueField A) ⟨_, hmem'⟩ (ρ b))) ∧

          (∃ (γ' : SL(2, ℤ)) (_ : γ' ∈ CongruenceSubgroup.Gamma q) (_ : γ' ∈ CongruenceSubgroup.Gamma0 M') (τ' : ↥K ≃ₐ[L] ↥K)
             (_ : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') γ'⁻¹ K τ')
             (_ : (∀ (b : ↥(chartAlgFin A (↥K) j)) (hb : τ' (b : ↥K) ∈ chartAlgFin A (↥K) j),
                  b ∈ y ↔ (⟨τ' (b : ↥K), hb⟩ : ↥(chartAlgFin A (↥K) j)) ∈ y))
             (hmem' : ((1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)), (-1 : (GaloisField q 2)ˣ)) ∈ DrinfeldCurve.hSubgroup q),
             ∀ (b : ↥B) (hb : τ' (b : ↥K) ∈ B), ρ ⟨τ' (b : ↥K), hb⟩ = DrinfeldCurve.hAction q (ResidueField A) ⟨_, hmem'⟩ (ρ b)) := by sorry
