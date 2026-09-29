-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_blowupChart_drinfeldFibre_hAction_of_semilinear_chartAut_of_fibrePackage_of_dvd
-- name    : ModularCurve.FullLevel.AuxLevelOne.blowupChart_drinfeldFibre_hAction_of_semilinear_chartAut_of_fibrePackage_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:14.444979+00:00
-- url     : https://prove2.me/theorems/0c5d5b51-41bc-5383-b503-4e6d4716665d
-- title:
--   Semilinear chart automorphisms act through `hAction` on the Drinfeld fibre
-- statement:
--   **Level and coefficient data.** Let $q$ be a prime, $M'$ a positive integer with $q \nmid M'$, and $\ell$ a prime with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$. Let $L$ be a field of characteristic zero and $\zeta \in L$ a primitive $q$-th root of unity, and assume (`hι`) that there is a ring homomorphism $\iota_0 : L \to \mathbb{C}$ with $\iota_0(\zeta) = e^{2\pi i/q}$. Let $H_1 \le (\mathbb{Z}/q^2M')^\times$ be a subgroup which (`hH₁`) is the intersection of [`ModularCurve.FullLevel.levelH q M'`](def/ModularCurve_FullLevelJacobian.html#L22), the kernel of the reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$, with the kernel of the reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/\ell)^\times$; so $H_1$ is the group of units congruent to $1$ both modulo $q$ and modulo $\ell$. Let $K$ be an intermediate field of $L \subseteq L((T))$ which (`hK`) equals [`ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField (q^2*M') H₁)`](def/ModularCurve_LaurentCoeff.html#L103), i.e. the subfield of $L((T))$ generated over $L$ by the image, under the coefficientwise map $\mathbb{Q} \to L$, of the field of $q$-expansions of modular functions for $\Gamma_{H_1}(q^2M')$ over $\mathbb{Q}$.
--
--   **Base ring and the chart algebra.** Let $A$ be a henselian discrete valuation domain with fraction field $L$ and algebraically closed residue field, with $q \in \mathfrak{m}_A$ (`hAq`) and $\zeta$ in the image of $A$ (`hζA`), and let $K$ be an $A$-algebra compatibly with $L$. Let $j \in K$ be nonzero with Laurent expansion the image under [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81) of [`ModularCurve.jq`](def/ModularCurve_X0.html#L157), the $q$-expansion of the modular $j$-function. Let $\varpi$ generate $\mathfrak{m}_A$, and let $\varpi_t \in A$ satisfy $\varpi_t^{\,q^2-1} = q\,u$ for some unit $u$ (`hϖt`). Write $C :=$ `chartAlgFin A K j`, the $A$-subalgebra of $K$ of elements integral over $A[j]$, and `jChartFin` for $j$ viewed in $C$. Let $y \subset C$ be a maximal ideal containing the image of $\varpi$, and assume (`hss`) that for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi : C \to \Omega$ with kernel exactly $y$ one has $\varphi(j) \in$ [`ModularCurve.ssJSet q Ω`](def/ModularCurve_SupersingularModuli.html#L7), that is: every elliptic Weierstrass curve over $\Omega$ with $j$-invariant $\varphi(j)$ has no nonzero point killed by $q$.
--
--   **The two-chart model.** Let $X :=$ [`AlgebraicCurve.TwoChartIntegralModel A K j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236), the pushout of $\operatorname{Spec}$ of the two chart algebras $C$ and `chartAlgInf A K j` (elements integral over $A[j^{-1}]$) along the middle chart, with structure morphism `toBase` to $\operatorname{Spec} A$. Let $z \in X$ and let $\varpi_z$ be (`hϖz`) the germ at $z$ of the global section of $X$ obtained from $\varpi$ through `toBase`; assume $\varpi_z$ lies in the maximal ideal of the stalk $\mathcal{O}_{X,z}$ (`hz`). Let $y'$ be a point of `XFin` $= \operatorname{Spec} C$ with `ιFin` sending $y'$ to $z$ (`hy'`), satisfying the same supersingularity condition at $y'.\mathrm{asIdeal}$ (`hss'`), and with $y'.\mathrm{asIdeal} = y$ (`hy'y`).
--
--   **The completed Drinfeld chart.** Let $W_1$ be a complete discrete valuation domain, $\sigma_1 : A \to W_1$ a ring homomorphism with $\mathfrak{m}_{W_1} = (\sigma_1\varpi)$, and let $f_1, u_1, v_1 \in W_1[[X_0,X_1]]$ with $u_1, v_1$ units and $f_1 \equiv X_0X_1^q - X_0^qX_1$ (the form [`DrinfeldCurve.LocalChart.drinfeldForm q W₁`](def/DrinfeldCurve_LocalChart.html#L18)) modulo $(X_0,X_1)^{q+2}$. Put
--   $$S := W_1[[X_0,X_1]]\big/\big(C(\sigma_1(\varpi_t^{\,q+1}))\,v_1 - f_1u_1\big),$$
--   with quotient map $\mathrm{mk}_S$, and let $e_1$ be a ring isomorphism from the $\mathfrak{m}$-adic completion $\widehat{\mathcal{O}}_{X,z}$ onto $S$. Write $\mathrm{toC} : \mathcal{O}_{X,z} \to \widehat{\mathcal{O}}_{X,z}$ for the completion map and $\mathrm{germ}_Y : C \to \mathcal{O}_{X,z}$ for the canonical map coming from the identification of $C$ with the sections of $X$ over the image of `ιFin` followed by the germ at $z$.
--
--   **The hypothesis `hW₁`** is a conjunction of seven clauses. (i) For $a \in A$, $e_1$ carries the image of $a$ in $\widehat{\mathcal{O}}_{X,z}$ to $\mathrm{mk}_S(C(\sigma_1 a))$. (ii) For $\gamma \in \Gamma_0(M')$ and every $L$-algebra automorphism $\tau$ of $K$ satisfying [`ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q^2*M') H₁ γ⁻¹ K τ`](def/ModularCurve_FullLevelLevelAutAt.html#L29), the automorphism $\tau$ maps $C$ into $C$. Here the latter predicate says: for every weight $k \in \mathbb{Z}$, every pair $f,g$ of modular forms of weight $k$ for $\Gamma_{H_1}(q^2M')$ (as a subgroup of $\mathrm{GL}_2(\mathbb{R})$ through [`CohCarrier.GammaH`](def/CohCarrier_Level.html#L133)), every pair of power series $p_f,p_g \in \mathbb{Z}[[T]]$ that are the $q$-expansions of $f$ and $g$ with the Laurent series of $p_g$ over $\mathbb{Q}$ nonzero, every $x \in K$ whose Laurent expansion is the image under `coeffEmb L` of the quotient of those Laurent series, and every ring homomorphism $\iota : L \to \mathbb{C}$ with $\iota(\zeta) = e^{2\pi i/q}$, the series $\iota_*(\tau x)$ times the $q$-expansion of $g\mid_k \mathrm{conjElemN}\,q\,\gamma^{-1}$ equals the $q$-expansion of $f\mid_k \mathrm{conjElemN}\,q\,\gamma^{-1}$, where $\mathrm{conjElemN}\,q\,\delta$ is the matrix $\begin{pmatrix} \delta_{00} & \delta_{01}/q \\ q\delta_{10} & \delta_{11}\end{pmatrix}$. (iii) For $\gamma \in \Gamma_0(M')$ with $\gamma_{11} \equiv 1 \pmod{\ell}$ and $\tau$ as in (ii) preserving $C$, the induced endomorphism of $C$ is congruent to the identity modulo $y$. (iv) For $\gamma \in \Gamma_0(M')$ and $\tau$ as in (ii) preserving $C$ and congruent to the identity modulo $y$, there exist a ring automorphism $\theta$ of $S$, an element $c \in W_1$ and a matrix $M \in \mathrm{M}_2(W_1)$ such that: $\theta \circ e_1 \circ \mathrm{toC} \circ \mathrm{germ}_Y = e_1 \circ \mathrm{toC} \circ \mathrm{germ}_Y \circ \tau$ on $C$; $\theta$ fixes $\mathrm{mk}_S(C(w))$ for all $w \in W_1$; $\theta(\mathrm{mk}_S X_j) \equiv \mathrm{mk}_S\big(\sum_i C(M_{ij})X_i\big)$ modulo $(\mathrm{mk}_S X_0, \mathrm{mk}_S X_1)^2$; $c^{q+1} \equiv 1$ and $M_{ij} \equiv c\,\gamma_{ij}$ modulo $\mathfrak{m}_{W_1}$; if $\gamma_{11} \equiv 1 \pmod{\ell}$ then $c \equiv 1$ modulo $\mathfrak{m}_{W_1}$; and if $\gamma \in \Gamma(q)$ and $\tau$ is not the identity then $c \not\equiv 1$ modulo $\mathfrak{m}_{W_1}$. (v) For integers $a_1,b_1,a_2,b_2$ and primes $P_1,P_2$ of $S$, each omitting at least one of $\mathrm{mk}_S X_0, \mathrm{mk}_S X_1$, each containing $\mathrm{mk}_S(C(\sigma_1\varpi))$, and each containing an element $\mathrm{mk}_S(C(a_i)X_0 + C(b_i)X_1 + h)$ with $h \in (X_0,X_1)^2$, with $q \nmid a_1b_2 - a_2b_1$, the contractions of $P_1$ and $P_2$ to $\mathcal{O}_{X,z}$ along $e_1 \circ \mathrm{toC}$ are distinct. (vi) For a prime $P$ of $S$ omitting one of $\mathrm{mk}_S X_0, \mathrm{mk}_S X_1$, containing $\mathrm{mk}_S(C(\sigma_1\varpi))$ and containing some $\mathrm{mk}_S(X_0 + h)$ with $h \in (X_0,X_1)^2$, and for $a \in C$: the germ $\mathrm{toC}(\mathrm{germ}_Y(a))$ lies in the contraction of $P$ along $e_1$ if and only if every Laurent coefficient of $a$ lies in the image of $\mathfrak{m}_A$ in $L$. (vii) There exist a proof that [`ModularCurve.jqNModC L q`](def/ModularCurve_JqCoeff.html#L18) — the $q$-expansion of $j$ with the Tate parameter replaced by its $q$-th power — lies in $K$ and in $C$, an element $a_0 \in A$ with $\mathrm{jqNModC} - a_0 \in y$, an integer $e_0 \ge 1$ and $h \in (X_0,X_1)^{e_0}$ such that for all $a,b \in W_1$ not both in $\mathfrak{m}_{W_1}$ with $a^qb - ab^q \in \mathfrak{m}_{W_1}$ the value $\sum_{i=0}^{e_0} (\text{coefficient of } X_0^iX_1^{e_0-i} \text{ in } h)\,a^ib^{e_0-i}$ is a unit, and such that $e_1(\mathrm{toC}(\mathrm{germ}_Y(\mathrm{jqNModC} - a_0))) = \mathrm{mk}_S(h)$.
--
--   **The blow-up ideal and chart.** Let $J \subseteq C$ be the ideal which (`hJ`) is the infimum of all ideals of the form $\tau^{-1}\big((e_1\circ \mathrm{toC}\circ \mathrm{germ}_Y)^{-1}(\mathrm{mk}_S(C(\sigma_1\varpi_t), X_0, X_1))\big)$, where $\gamma$ runs over $\Gamma(q) \cap \Gamma_0(M')$ and $\tau$ over the level automorphisms at $\gamma^{-1}$ in the above sense which preserve $C$. Let $B \subseteq K$ be the $A$-subalgebra which (`hB`) is the $C$-subalgebra generated by $\{x \in K : \exists\, i \in J,\ x\varpi_t = i\}$, i.e. $B = C[J/\varpi_t]$, with $C \le B$ (`hCB`).
--
--   **The hypothesis `hbridge`** (eight clauses) requires, with $\mathfrak{M} := (\mathrm{mk}_S(C(\sigma_1\varpi)), \mathrm{mk}_S X_0, \mathrm{mk}_S X_1) \subseteq S$ and $\Psi := e_1\circ\mathrm{toC}\circ\mathrm{germ}_Y : C \to S$: that $\Psi^{-1}(\mathfrak{M}) = y$; that for all $n$ and all $s \in S$ some $a \in C$ has $\Psi(a) - s \in \mathfrak{M}^n$; that $\Psi(a) = \mathrm{mk}_S(C(\sigma_1 a))$ for $a \in A$; that every element of $C$ is congruent modulo $y$ to an element of $A$; that every element of $W_1$ is congruent modulo $\mathfrak{m}_{W_1}$ to an element of $\sigma_1(A)$; that $\sigma_1^{-1}(\mathfrak{m}_{W_1}) = \mathfrak{m}_A$; that $\mathfrak{M}$ is maximal and is the only maximal ideal of $S$; and that $S$ is flat over $C$ through $\Psi$.
--
--   **The hypothesis `hcentre`** (four clauses) requires that $\Psi(J)$ generate $(\mathrm{mk}_S(C(\sigma_1\varpi_t)), \mathrm{mk}_S X_0, \mathrm{mk}_S X_1)$; that $J = \Psi^{-1}\big((\mathrm{mk}_S(C(\sigma_1\varpi_t)), \mathrm{mk}_S X_0, \mathrm{mk}_S X_1)\big) \cap I$ for some ideal $I$ of $C$ with $I + y = C$; that $J \subseteq y$; and that the image of $\varpi_t$ lies in $J$. Finally, an $\mathbb{F}_{q^2}$-algebra structure on the residue field $\kappa_A$ of $A$ is fixed (`inst`).
--
--   **Conclusion.** Let $L_{\mathrm{loc}} :=$ `Localization.Away (mk_S(C(σ₁ϖt)))`, let $\iota_S : S \to L_{\mathrm{loc}}$ be the localisation map, put $x_0 := \iota_S(\mathrm{mk}_S X_0)\cdot \mathrm{mk}_S(C(\sigma_1\varpi_t))^{-1}$ and $x_1 := \iota_S(\mathrm{mk}_S X_1)\cdot \mathrm{mk}_S(C(\sigma_1\varpi_t))^{-1}$, and let $R_{\mathrm{loc}} \subseteq L_{\mathrm{loc}}$ be the subring generated by the image of $\iota_S$ together with $x_0$ and $x_1$. Then the following holds for every ring homomorphism $\Phi : B \to L_{\mathrm{loc}}$, every witness that the image of $\iota_S$, the elements $x_0, x_1$ and the image of $\Phi$ all lie in $R_{\mathrm{loc}}$, and all data $t_W : W_1 \to \kappa_A$ (a ring homomorphism), $c_R \in \kappa_A$, $\rho_R : R_{\mathrm{loc}} \to$ [`DrinfeldCurve.CoordRing q κ_A`](def/DrinfeldCurve_CoordRing.html#L21) and $\rho : B \to$ [`DrinfeldCurve.CoordRing q κ_A`](def/DrinfeldCurve_CoordRing.html#L21), where the Drinfeld coordinate ring is $\kappa_A[X_0,X_1]$ modulo `drinfeldPoly q κ_A - 1` with distinguished elements [`DrinfeldCurve.x`](def/DrinfeldCurve_CoordRing.html#L42) and [`DrinfeldCurve.y`](def/DrinfeldCurve_CoordRing.html#L44): assume that $\Phi$ restricted to $C$ agrees with $\iota_S \circ \Psi$; that for $x \in B$ and $i \in J$ with $x\varpi_t = i$ in $K$ one has $\Phi(x)\cdot\iota_S(\mathrm{mk}_S(C(\sigma_1\varpi_t))) = \iota_S(\Psi(i))$; that $t_W \circ \sigma_1$ is the residue map of $A$ and $t_W$ kills $\mathfrak{m}_{W_1}$; that $c_R \neq 0$; that $\rho_R(\iota_S(\mathrm{mk}_S F))$ is the image in the coordinate ring of $t_W(\mathrm{constantCoeff}\,F)$ for every $F \in W_1[[X_0,X_1]]$; that $\rho_R(x_0) = c_R\cdot x$ and $\rho_R(x_1) = c_R\cdot y$; and that $\rho = \rho_R \circ \Phi$ on $B$.
--
--   Then for every ring automorphism $\tau$ of $K$ mapping $C$ into $C$ and $B$ into $B$, every ring automorphism $\theta$ of $S$, every ring automorphism $\sigma_W$ of $W_1$, all $t_a, t_m \in W_1$, every $M \in \mathrm{M}_2(W_1)$, every $g \in \mathrm{GL}_2(\mathbb{Z}/q)$ and $c \in \mathbb{F}_{q^2}^\times$ with $(g,c) \in$ [`DrinfeldCurve.hSubgroup q`](def/DrinfeldCurve_CoordRing.html#L276) (the kernel of $(g,c) \mapsto \det(g)\cdot c^{q+1}$ in $\mathbb{F}_{q^2}^\times$, the determinant being read through $(\mathbb{Z}/q)^\times \to \mathbb{F}_{q^2}^\times$), subject to: $\theta \circ \Psi = \Psi \circ \tau$ on $C$; $\theta(\mathrm{mk}_S(C(w))) = \mathrm{mk}_S(C(\sigma_W w))$ for all $w \in W_1$; $\sigma_W(w) \equiv w$ modulo $\mathfrak{m}_{W_1}$ for all $w$; $t_a$ a unit, $t_m \in \mathfrak{m}_{W_1}$ and $\sigma_W(\sigma_1\varpi_t) = t_a\,\sigma_1\varpi_t\,(1+t_m)$; $\theta(\mathrm{mk}_S X_j) \equiv \mathrm{mk}_S\big(\sum_i C(M_{ij})X_i\big)$ modulo $(\mathrm{mk}_S X_0,\mathrm{mk}_S X_1)^2$ for $j = 0,1$; and $t_W(M_{ij}) = t_W(t_a)\cdot c\cdot \overline{g_{ij}}$ in $\kappa_A$ for all $i,j$, where $c$ is taken through $\mathbb{F}_{q^2} \to \kappa_A$ and $\overline{g_{ij}}$ is the image of the representative of $g_{ij} \in \mathbb{Z}/q$ — it follows that for every $b \in B$ with $\tau(b) \in B$,
--   $$\rho(\tau b) = \mathrm{hAction}_q(\kappa_A)\big((g,c)\big)\,(\rho\,b),$$
--   the action of $(g,c)$ on [`DrinfeldCurve.CoordRing q κ_A`](def/DrinfeldCurve_CoordRing.html#L21) by the homomorphism [`DrinfeldCurve.hAction`](def/DrinfeldCurve_CoordRing.html#L325).
--
--   The automorphism $\tau$ in the conclusion is only required to be a ring automorphism of $K$ preserving $C$ and $B$, with a semilinear lift $\theta$ of the stated shape; the level-theoretic conditions enter solely through `hW₁`, `hJ`, `hbridge` and `hcentre`.
--
--   This is the transfer step which identifies, on the Drinfeld fibre of the blow-up chart $B = C[J/\varpi_t]$ over the supersingular point $y$, the effect of a chart automorphism that is semilinear with linear part congruent to $t_a\,c\,g$ with the action of $(g,c)$ on the Drinfeld coordinate ring $\kappa_A[x,y]/(xy^q - x^qy - 1)$, for an arbitrary fibre package $(\Phi, t_W, c_R, \rho_R, \rho)$. It is the variant for the auxiliary level $\Gamma_{H_1}(q^2M')$ cut out by the diamond condition at a prime $\ell \equiv 11 \pmod{12}$, and is used in the analysis of the inertia action in the decomposition of the Drinfeld chart at a supersingular point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevelOne_blowupChart_drinfeldFibre_hAction_of_semilinear_chartAut_of_fibrePackage_of_dvd.lean

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

theorem ModularCurve.FullLevel.AuxLevelOne.blowupChart_drinfeldFibre_hAction_of_semilinear_chartAut_of_fibrePackage_of_dvd
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
