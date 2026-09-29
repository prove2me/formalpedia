-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevel_blowupChart_drinfeldFibre_hAction_of_semilinear_chartAut_of_fibrePackage
-- name    : ModularCurve.FullLevel.AuxLevel.blowupChart_drinfeldFibre_hAction_of_semilinear_chartAut_of_fibrePackage
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:14.444979+00:00
-- url     : https://prove2.me/theorems/aa44d71b-e408-5a84-9802-3cb91c57f437
-- title:
--   Semilinear chart automorphisms act on the Drinfeld fibre through H
-- statement:
--   **Setting.** Fixed are primes $q\ge 5$ and $\ell\ge 3$ with $\ell\neq q$, and a nonzero natural number $M'$ divisible by neither $q$ nor $\ell$; a field $L$ of characteristic $0$ with a primitive $(q\ell)$-th root of unity $\xi$, subject to the hypothesis `hι` that some ring homomorphism $\iota:L\to\mathbb C$ carries $\xi$ to $e^{2\pi i/(q\ell)}$; and an intermediate field $K$ of $L\subseteq$ `LaurentSeries L`, required by `hK` to equal [`ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField ((q*ℓ)^2*M') (ModularCurve.FullLevel.levelH (q*ℓ) M'))`](def/ModularCurve_LaurentCoeff.html#L103), i.e. the subfield of $L((t))$ generated over $L$ by the image, under the coefficientwise map [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81), of the field of $q$-expansions over $\mathbb Q$ attached to $X_H$ of level $N_0=(q\ell)^2M'$ with $H=$ [`ModularCurve.FullLevel.levelH (q*ℓ) M'`](def/ModularCurve_FullLevelJacobian.html#L22) the kernel of $(\mathbb Z/N_0)^\times\to(\mathbb Z/q\ell)^\times$, that is the units congruent to $1$ modulo $q\ell$.
--
--   Further, $A$ is a Henselian discrete valuation ring which is a domain with algebraically closed residue field and fraction field $L$, such that $q\in\mathfrak m_A$ (`hAq`) and $\xi$ lies in the image of $A$ (`hξA`), together with an $A$-algebra structure on $K$ compatible with that on $L$; $\varpi$ is a generator of $\mathfrak m_A$ (`hϖ`), and $\varpi_t\in A$ satisfies $\varpi_t^{\,q^2-1}=q\,u$ for some unit $u$ (`hϖt`). The element $j\in K$ is nonzero and has Laurent expansion [`ModularCurve.coeffEmb L ModularCurve.jq`](def/ModularCurve_LaurentCoeff.html#L81), the $q$-expansion of the modular invariant. Write $C:=$ `chartAlgFin A (↥K) j`, the $A$-subalgebra of $K$ consisting of the elements integral over $A[j]$, and `jChartFin A (↥K) j` for $j$ viewed in $C$.
--
--   **The supersingular point.** A maximal ideal $y$ of $C$ is given with $\varpi\in y$ (`hϖy`) and with the hypothesis `hss`: for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi:C\to\Omega$ with kernel $y$, the element $\varphi(j)$ lies in [`ModularCurve.ssJSet q Ω`](def/ModularCurve_SupersingularModuli.html#L7), the set of $\bar j\in\Omega$ such that every elliptic Weierstrass curve over $\Omega$ with $j$-invariant $\bar j$ has no nonzero $q$-torsion point. On the two-chart integral model $X:=$ [`AlgebraicCurve.TwoChartIntegralModel A (↥K) j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) (the pushout gluing $\operatorname{Spec}C$ and $\operatorname{Spec}$ of the chart algebra at $j^{-1}$ along the middle chart), a point $z$ is given such that the germ $\varpi_z$ at $z$ of the global section of $X$ obtained from $\varpi$ through `toBase` lies in the maximal ideal of the stalk (hypotheses `hϖz`, `hz`), together with a point $y'$ of `XFin A (↥K) j` with `ιFin`-image $z$ (`hy'`), satisfying the same supersingularity hypothesis `hss'` for $y'.\mathrm{asIdeal}$, and $y'.\mathrm{asIdeal}=y$ (`hy'y`).
--
--   **The Drinfeld chart at $z$.** $W_1$ is a complete discrete valuation domain, $\sigma_1:A\to W_1$ a ring homomorphism with $\mathfrak m_{W_1}=(\sigma_1\varpi)$ (`hσ₁`); $u_1,v_1\in W_1[[X_0,X_1]]$ are units and $f_1\in W_1[[X_0,X_1]]$ satisfies $f_1\equiv$ [`DrinfeldCurve.LocalChart.drinfeldForm q W₁`](def/DrinfeldCurve_LocalChart.html#L18) $=X_0X_1^q-X_0^qX_1$ modulo $(X_0,X_1)^{q+2}$ (`hf₁`). Put
--   $$S:=W_1[[X_0,X_1]]\big/\big(C(\sigma_1(\varpi_t^{\,q+1}))\,v_1-f_1u_1\big),$$
--   with quotient map $\mathrm{mk}_S$, and $e_1$ is a ring isomorphism from the adic completion $\mathrm{CMP}$ of the stalk $\mathrm{STK}:=\mathcal O_{X,z}$ at its maximal ideal onto $S$. Let $\mathrm{toC}:\mathrm{STK}\to\mathrm{CMP}$ be the completion map, $\mathrm{germY}:C\to\mathrm{STK}$ the canonical homomorphism coming from the identification of the global sections of $\operatorname{Spec}C$ with $C$ and the open immersion `ιFin`, and $\Psi:=e_1\circ\mathrm{toC}\circ\mathrm{germY}:C\to S$.
--
--   **The hypothesis `hW₁`** is a conjunction of seven clauses, stated in terms of these data. (i) For $a\in A$, $\Psi$ applied to the germ at $z$ of $a$ (through `toBase`) is $\mathrm{mk}_S(C(\sigma_1 a))$. (ii) For every $\gamma\in\Gamma_0(M')$ and every $L$-algebra automorphism $\tau$ of $K$ with [`ModularCurve.FullLevel.IsLevelAutAt L (q*ℓ) ξ (q*ℓ) ((q*ℓ)^2*M') (ModularCurve.FullLevel.levelH (q*ℓ) M') γ⁻¹ K τ`](def/ModularCurve_FullLevelLevelAutAt.html#L29) — that is, $\tau$ realises on $q$-expansions, under every embedding $\iota:L\to\mathbb C$ with $\iota\xi=e^{2\pi i/(q\ell)}$, the substitution by the matrix `conjElemN (q*ℓ) γ⁻¹` on all quotients $f/g$ of weight-$k$ modular forms for $\Gamma_H(N_0)$ with integral $q$-expansions — one has $\tau(C)\subseteq C$. (iii) If moreover $\gamma\in\Gamma(\ell)$, the induced endomorphism of $C$ is congruent to the identity modulo $y'.\mathrm{asIdeal}$. (iv) For $\gamma\in\Gamma_0(M')$ and such a $\tau$ preserving $C$ and congruent to the identity modulo $y'.\mathrm{asIdeal}$, there exist a ring automorphism $\theta$ of $S$, an element $c\in W_1$ and a matrix $M$ over $W_1$ indexed by $\mathrm{Fin}\,2$ such that $\theta\circ\Psi=\Psi\circ\tau|_C$; $\theta$ fixes all constants $\mathrm{mk}_S(C(w))$; $\theta(\mathrm{mk}_S X_j)\equiv\mathrm{mk}_S(\sum_i C(M_{ij})X_i)$ modulo the square of the ideal generated by $\mathrm{mk}_SX_0,\mathrm{mk}_SX_1$; $c^{q+1}\equiv1$ and $M_{ij}\equiv c\,\gamma_{ij}$ modulo $\mathfrak m_{W_1}$; $\gamma\in\Gamma(\ell)$ forces $c\equiv1$; and $\gamma\in\Gamma(q)$ together with $\tau\neq\mathrm{id}$ forces $c\not\equiv1$ modulo $\mathfrak m_{W_1}$. (v) For integers $a_1,b_1,a_2,b_2$ and prime ideals $P_1,P_2$ of $S$, each omitting at least one of $\mathrm{mk}_SX_0,\mathrm{mk}_SX_1$, each containing $\mathrm{mk}_S(C(\sigma_1\varpi))$, and each containing an element $\mathrm{mk}_S(C(a_i)X_0+C(b_i)X_1+h)$ with $h\in(X_0,X_1)^2$, if $q\nmid a_1b_2-a_2b_1$ then the contractions of $P_1$ and $P_2$ to $\mathrm{STK}$ along $e_1\circ\mathrm{toC}$ are distinct. (vi) For a prime $P$ of $S$ omitting at least one of $\mathrm{mk}_SX_0,\mathrm{mk}_SX_1$, containing $\mathrm{mk}_S(C(\sigma_1\varpi))$ and containing some $\mathrm{mk}_S(C(1)X_0+C(0)X_1+h)$ with $h\in(X_0,X_1)^2$, and for $a\in C$: $\mathrm{toC}(\mathrm{germY}\,a)$ lies in the contraction of $P$ along $e_1$ if and only if every Laurent coefficient of $a$, viewed in $L((t))$, lies in the image of $\mathfrak m_A$. (vii) The element [`ModularCurve.jqNModC L (q*ℓ)`](def/ModularCurve_JqCoeff.html#L18) — the $q$-expansion `jqModC L` of $j$ with all exponents multiplied by $q\ell$ — lies in $K$ and in $C$, and there are $a_0\in A$ with that element congruent to $a_0$ modulo $y'.\mathrm{asIdeal}$, an integer $e_0\ge1$ and $h\in(X_0,X_1)^{e_0}$ such that, first, for all $a,b\in W_1$ not both in $\mathfrak m_{W_1}$ with $a^qb-ab^q\in\mathfrak m_{W_1}$ the sum $\sum_{i=0}^{e_0}\mathrm{coeff}_{(i,\,e_0-i)}(h)\,a^ib^{e_0-i}$ is a unit, and second, $\Psi$ of that element minus $a_0$ equals $\mathrm{mk}_S h$.
--
--   **The blow-up chart.** The ideal $J$ of $C$ is required by `hJ` to be the infimum of all ideals of the form $(\tau|_C)^{-1}\big(\Psi^{-1}(\mathrm{span}\{\mathrm{mk}_S(C(\sigma_1\varpi_t)),\mathrm{mk}_SX_0,\mathrm{mk}_SX_1\})\big)$, taken over all $\gamma\in\Gamma(q)\cap\Gamma_0(M')$ and all $L$-algebra automorphisms $\tau$ of $K$ satisfying `IsLevelAutAt` at $\gamma^{-1}$ and preserving $C$. The $A$-subalgebra $B$ of $K$ is required by `hB` to be the scalar restriction to $A$ of the $C$-subalgebra of $K$ generated by $\{x\in K:\exists\,i\in J,\ x\varpi_t=i\}$, i.e. $B=C[J/\varpi_t]$, and `hCB` requires $C\le B$.
--
--   The hypothesis `hbridge` is a conjunction of nine clauses: $\Psi^{-1}$ of $\mathfrak n:=\mathrm{span}\{\mathrm{mk}_S(C(\sigma_1\varpi)),\mathrm{mk}_SX_0,\mathrm{mk}_SX_1\}$ equals $y$; $\Psi(C)$ is dense, in that for all $n$ and all $s\in S$ some $a\in C$ has $\Psi a-s\in\mathfrak n^n$; $\Psi(a)=\mathrm{mk}_S(C(\sigma_1a))$ for $a\in A$; every element of $C$ is congruent modulo $y$ to an element of $A$; every element of $W_1$ is congruent modulo $\mathfrak m_{W_1}$ to an element of $\sigma_1(A)$; $\sigma_1^{-1}(\mathfrak m_{W_1})=\mathfrak m_A$; $\mathfrak n$ is maximal; every maximal ideal of $S$ equals $\mathfrak n$; and $S$ is flat over $C$ via $\Psi$. The hypothesis `hcentre` is a conjunction of four clauses: the ideal generated by $\Psi(J)$ is $\mathrm{span}\{\mathrm{mk}_S(C(\sigma_1\varpi_t)),\mathrm{mk}_SX_0,\mathrm{mk}_SX_1\}$; there is an ideal $I$ of $C$ with $J=\Psi^{-1}(\mathrm{span}\{\mathrm{mk}_S(C(\sigma_1\varpi_t)),\mathrm{mk}_SX_0,\mathrm{mk}_SX_1\})\cap I$ and $I+y=C$; $J\le y$; and $\varpi_t\in J$. Finally the residue field of $A$ carries an algebra structure over `GaloisField q 2`.
--
--   **Conclusion.** Set $\mathrm{Lloc}:=$ `Localization.Away (mkS (MvPowerSeries.C (σ₁ ϖt)))` with canonical map $\iota_S:S\to\mathrm{Lloc}$, put $x_0:=\iota_S(\mathrm{mk}_SX_0)\cdot(\sigma_1\varpi_t)^{-1}$ and $x_1:=\iota_S(\mathrm{mk}_SX_1)\cdot(\sigma_1\varpi_t)^{-1}$ using the inverse of the localised element, and let $R_{\mathrm{loc}}$ be the subring of $\mathrm{Lloc}$ generated by the image of $\iota_S$ together with $x_0,x_1$. Then the following holds for every ring homomorphism $\Phi:B\to\mathrm{Lloc}$, every witnessing of the memberships $\iota_S(S)\subseteq R_{\mathrm{loc}}$, $x_0,x_1\in R_{\mathrm{loc}}$ and $\Phi(B)\subseteq R_{\mathrm{loc}}$, and all $t_W:W_1\to\kappa_A$, $c_R\in\kappa_A$, $\rho_R:R_{\mathrm{loc}}\to\mathcal R$ and $\rho:B\to\mathcal R$, where $\kappa_A$ is the residue field of $A$ and $\mathcal R:=$ [`DrinfeldCurve.CoordRing q (ResidueField A)`](def/DrinfeldCurve_CoordRing.html#L21) is the quotient of $\kappa_A[X_0,X_1]$ by the ideal generated by `drinfeldPoly q (ResidueField A)` $-1$, with classes [`DrinfeldCurve.x q (ResidueField A)`](def/DrinfeldCurve_CoordRing.html#L42) and [`DrinfeldCurve.y q (ResidueField A)`](def/DrinfeldCurve_CoordRing.html#L44) of the coordinates, subject to the fibre-package hypotheses: $\Phi$ restricted to $C$ equals $\iota_S\circ\Psi$; for $x\in B$ and $i\in J$ with $x\varpi_t=i$ in $K$ one has $\Phi(x)\cdot\iota_S(\mathrm{mk}_S(C(\sigma_1\varpi_t)))=\iota_S(\Psi i)$; $t_W(\sigma_1a)$ is the residue of $a$ for $a\in A$ and $t_W$ kills $\mathfrak m_{W_1}$; $c_R\neq0$; $\rho_R(\iota_S(\mathrm{mk}_SF))$ is the image in $\mathcal R$ of $t_W(\mathrm{constantCoeff}\,F)$ for every $F\in W_1[[X_0,X_1]]$; $\rho_R(x_0)=c_R\cdot x$ and $\rho_R(x_1)=c_R\cdot y$; and $\rho=\rho_R\circ\Phi$ on $B$.
--
--   Under these hypotheses, for every ring automorphism $\tau$ of $K$ with $\tau(C)\subseteq C$ and $\tau(B)\subseteq B$, every ring automorphism $\theta$ of $S$, every ring automorphism $\sigma_W$ of $W_1$, all $t_a,t_m\in W_1$, every matrix $M$ over $W_1$ indexed by $\mathrm{Fin}\,2$, every $g\in\mathrm{GL}_2(\mathbb Z/q)$ and every unit $c$ of $\mathbb F_{q^2}$ with $(g,c)\in$ [`DrinfeldCurve.hSubgroup q`](def/DrinfeldCurve_CoordRing.html#L276), i.e. $(g,c)$ in the kernel of [`DrinfeldCurve.hChar q`](def/DrinfeldCurve_CoordRing.html#L265), so that the image of $\det g$ in $\mathbb F_{q^2}^\times$ times $c^{q+1}$ is $1$, such that
--
--   - $\theta\circ\Psi=\Psi\circ\tau|_C$ on $C$;
--
--   - $\theta(\mathrm{mk}_S(C(w)))=\mathrm{mk}_S(C(\sigma_Ww))$ for all $w\in W_1$, with $\sigma_Ww\equiv w$ modulo $\mathfrak m_{W_1}$;
--
--   - $t_a$ is a unit, $t_m\in\mathfrak m_{W_1}$ and $\sigma_W(\sigma_1\varpi_t)=t_a\,\sigma_1\varpi_t\,(1+t_m)$;
--
--   - $\theta(\mathrm{mk}_SX_j)\equiv\mathrm{mk}_S(\sum_iC(M_{ij})X_i)$ modulo the square of the ideal generated by $\mathrm{mk}_SX_0,\mathrm{mk}_SX_1$;
--
--   - $t_W(M_{ij})=t_W(t_a)\cdot\bar c\cdot\bar g_{ij}$ in $\kappa_A$ for all $i,j$, where $\bar c$ is the image of $c$ under $\mathbb F_{q^2}\to\kappa_A$ and $\bar g_{ij}$ the image of the canonical representative of $g_{ij}\in\mathbb Z/q$;
--
--   one has, for every $b\in B$ with $\tau b\in B$,
--   $$\rho(\tau b)=\big(\mathrm{DrinfeldCurve.hAction}\ q\ (\mathrm{ResidueField}\ A)\,(g,c)\big)(\rho\, b),$$
--   the action of $(g,c)$ by $\kappa_A$-algebra automorphisms of $\mathcal R$.
--
--   This is the semilinear form of the computation of the action on the Drinfeld fibre of the blow-up chart of the two-chart integral model at a supersingular point: a ring automorphism of the function field whose reading on the completed stalk is $\sigma_W$-semilinear, rescales the chart parameter $\varpi_t$ by a unit $t_a$ and has linear part reducing to $\bar t_a\,\bar c\,g$, acts on the coordinate ring of the Drinfeld curve over the residue field through the element $(g,c)$ of [`DrinfeldCurve.hSubgroup q`](def/DrinfeldCurve_CoordRing.html#L276). It is used in the downstream identification of the inertia and decomposition action at level $q\ell$ on the Drinfeld components of the model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevel_blowupChart_drinfeldFibre_hAction_of_semilinear_chartAut_of_fibrePackage.lean

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

theorem ModularCurve.FullLevel.AuxLevel.blowupChart_drinfeldFibre_hAction_of_semilinear_chartAut_of_fibrePackage
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

          ∀ (τ : ↥K ≃+* ↥K)
            (hτC : ∀ a : ↥K, a ∈ chartAlgFin A (↥K) j → τ a ∈ chartAlgFin A (↥K) j)
            (hτB : ∀ f : ↥K, f ∈ B → τ f ∈ B)
            (θ : S ≃+* S) (σW : W₁ ≃+* W₁) (ta tm : W₁) (M : Matrix (Fin 2) (Fin 2) W₁)
            (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)) (c : (GaloisField q 2)ˣ)
            (hmem : (g, c) ∈ DrinfeldCurve.hSubgroup q),

            (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
              θ (e₁ (toC (germY a))) = e₁ (toC (germY ((τ.toRingHom.restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
              (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hτC) a)))) →

            (∀ w : W₁, θ (mkS (MvPowerSeries.C w)) = mkS (MvPowerSeries.C (σW w))) →
            (∀ w : W₁, σW w - w ∈ IsLocalRing.maximalIdeal W₁) →

            IsUnit ta → tm ∈ IsLocalRing.maximalIdeal W₁ → σW (σ₁ ϖt) = ta * σ₁ ϖt * (1 + tm) →

            (∀ jj : Fin 2, θ (mkS (MvPowerSeries.X jj)) -
                mkS (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) ∈
              (Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2) →

            (∀ ii jj : Fin 2, tW (M ii jj) =
                tW ta * algebraMap (GaloisField q 2) (ResidueField A) ((c : (GaloisField q 2)ˣ) : GaloisField q 2) *
                  ((((g : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q)) ii jj).val : ResidueField A)) →

            ∀ (b : ↥B) (hb : τ (b : ↥K) ∈ B),
              ρ ⟨τ (b : ↥K), hb⟩ = DrinfeldCurve.hAction q (ResidueField A) ⟨(g, c), hmem⟩ (ρ b) := by sorry
