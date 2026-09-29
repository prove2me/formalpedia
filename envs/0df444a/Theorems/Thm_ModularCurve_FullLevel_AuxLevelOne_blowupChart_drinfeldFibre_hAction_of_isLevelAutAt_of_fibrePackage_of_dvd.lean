-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_blowupChart_drinfeldFibre_hAction_of_isLevelAutAt_of_fibrePackage_of_dvd
-- name    : ModularCurve.FullLevel.AuxLevelOne.blowupChart_drinfeldFibre_hAction_of_isLevelAutAt_of_fibrePackage_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:14.444979+00:00
-- url     : https://prove2.me/theorems/258ae79e-e545-5576-8d68-855b33ba281e
-- title:
--   Level automorphisms act on the Drinfeld fibre through H
-- statement:
--   **Arithmetic setting.** Here $q$ and $\ell$ are primes and $M'$ a non-zero natural number with $q \nmid M'$ (`hqM'`), $\ell \equiv 11 \pmod{12}$ (`hℓ12`) and $\ell \mid M'$ (`hℓM'`). The field $L$ has characteristic zero, $\zeta \in L$ is a primitive $q$-th root of unity (`hζ`), and `hι` asserts the existence of a ring homomorphism $\iota : L \to \mathbb{C}$ with $\iota(\zeta) = e^{2\pi i/q}$. The subgroup $H_1 \leq (\mathbb{Z}/q^2M')^{\times}$ is required (`hH₁`) to be the intersection of [`ModularCurve.FullLevel.levelH q M'`](def/ModularCurve_FullLevelJacobian.html#L22), the kernel of the reduction $(\mathbb{Z}/q^2M')^{\times} \to (\mathbb{Z}/q)^{\times}$, with the kernel of the reduction $(\mathbb{Z}/q^2M')^{\times} \to (\mathbb{Z}/\ell)^{\times}$. The intermediate field $K$ of $L \subseteq L((T))$ is required (`hK`) to be [`ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField (q^2*M') H₁)`](def/ModularCurve_LaurentCoeff.html#L103), i.e. the subfield generated over $L$ by the coefficientwise images in $L((T))$ of the elements of the $q$-expansion function field of $\Gamma_{H_1}(q^2M') \subseteq \mathrm{SL}_2(\mathbb{Z})$ over $\mathbb{Q}$.
--
--   The ring $A$ is a discrete valuation domain, Henselian local, with algebraically closed residue field $\kappa_A :=$ `ResidueField A` and fraction field $L$, and $K$ is an $A$-algebra compatibly with $L$; moreover $q \in \mathfrak{m}_A$ (`hAq`) and $\zeta$ lies in the image of $A$ in $L$ (`hζA`). The element $j \in K$ is non-zero and its image in $L((T))$ is the coefficientwise image of the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) of the modular invariant (`hj`). Finally $\varpi$ generates $\mathfrak{m}_A$ (`hϖ`), and $\varpi_t \in A$ satisfies $\varpi_t^{q^2-1} = q u$ for a unit $u$ (`hϖt`).
--
--   **Chart algebra and the supersingular point.** Write $C :=$ `chartAlgFin A ↥K j`, the $A$-subalgebra of $K$ consisting of the elements integral over $A[j]$, and `jChartFin` for $j$ regarded as an element of $C$. The ideal $y \subseteq C$ is maximal (`hy`) and contains $\varpi$ (`hϖy`), and `hss` requires that every ring homomorphism $\varphi$ from $C$ to an algebraically closed field $\Omega$ of characteristic $q$ with kernel $y$ sends $j$ into [`ModularCurve.ssJSet q Ω`](def/ModularCurve_SupersingularModuli.html#L7), the set of those $j_0 \in \Omega$ for which every elliptic curve over $\Omega$ with $j$-invariant $j_0$ has no point $P \neq 0$ with $q \cdot P = 0$.
--
--   **Integral model, stalk and formal chart.** Let $X :=$ [`AlgebraicCurve.TwoChartIntegralModel A ↥K j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236), the pushout of $\operatorname{Spec}$ of the two chart algebras (in $j$ and in $j^{-1}$) along $\operatorname{Spec}$ of the intermediate algebra, with structure morphism `toBase` to $\operatorname{Spec} A$. The point $z \in X$ is such that the germ $\varpi_z$ at $z$ of the global function obtained from $\varpi$ along `toBase` (`hϖz`) lies in the maximal ideal of the stalk (`hz`); $y'$ is a point of `XFin` $= \operatorname{Spec} C$ with `ιFin`-image $z$ (`hy'`), subject to the same supersingularity condition (`hss'`) and with $y'.\mathrm{asIdeal} = y$ (`hy'y`).
--
--   The ring $W_1$ is a complete discrete valuation domain, $\sigma_1 : A \to W_1$ a ring homomorphism with $\mathfrak{m}_{W_1} = (\sigma_1 \varpi)$ (`hσ₁`); $u_1, v_1 \in W_1[[X_0,X_1]]$ are units and $f_1$ is congruent to the Drinfeld form [`DrinfeldCurve.LocalChart.drinfeldForm`](def/DrinfeldCurve_LocalChart.html#L18) $= X_0X_1^q - X_0^qX_1$ modulo $(X_0,X_1)^{q+2}$ (`hf₁`); and $e_1$ is a ring isomorphism from the $\mathfrak{m}$-adic completion $\widehat{\mathcal{O}}_{X,z}$ onto
--   $$S := W_1[[X_0,X_1]]\big/\bigl(\sigma_1(\varpi_t^{q+1})\,v_1 - f_1 u_1\bigr).$$
--   In the statement the abbreviations `STK` $= \mathcal{O}_{X,z}$, `CMP` $= \widehat{\mathcal{O}}_{X,z}$, `toC` (the completion map), `mkS` (the quotient map onto $S$) and `germY` (the composite $C \to \mathcal{O}_{X,z}$ through the open immersion `ιFin`) are repeatedly introduced; write $\varepsilon := e_1 \circ \mathrm{toC} \circ \mathrm{germY} : C \to S$.
--
--   For $\gamma \in \mathrm{SL}_2(\mathbb{Z})$, the predicate [`ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q^2*M') H₁ γ⁻¹ K τ`](def/ModularCurve_FullLevelLevelAutAt.html#L29) says of an $L$-automorphism $\tau$ of $K$: for every weight $k$, all modular forms $f,g$ of weight $k$ on [`CohCarrier.GammaH (q^2*M') H₁`](def/CohCarrier_Level.html#L133) with integral $q$-expansion series $p_f, p_g$, with $p_g$ having non-zero Laurent series, every $x \in K$ whose Laurent expansion is $p_f/p_g$ and every embedding $\iota : L \to \mathbb{C}$ with $\iota(\zeta) = e^{2\pi i/q}$, the coefficientwise image $\iota_*(\tau x)$ multiplied by the $q$-expansion of $g \mid_k \alpha$ equals the $q$-expansion of $f \mid_k \alpha$, where $\alpha =$ `conjElemN q γ⁻¹` is the real matrix $\bigl(\begin{smallmatrix} (\gamma^{-1})_{00} & (\gamma^{-1})_{01}/q \\ q(\gamma^{-1})_{10} & (\gamma^{-1})_{11}\end{smallmatrix}\bigr)$. Such a $\tau$ is referred to below as a level automorphism attached to $\gamma^{-1}$.
--
--   **The hypothesis `hW₁` (seven clauses).** (i) For every $a \in A$, $e_1$ carries the image in $\widehat{\mathcal{O}}_{X,z}$ of the germ at $z$ of $a$ to the class of the constant series $\sigma_1(a)$. (ii) For every $\gamma \in \Gamma_0(M')$ and every level automorphism $\tau$ attached to $\gamma^{-1}$, $\tau$ maps $C$ into $C$. (iii) For every $\gamma \in \Gamma_0(M')$ with $\gamma_{11} \equiv 1 \pmod{\ell}$ and every level automorphism $\tau$ attached to $\gamma^{-1}$ preserving $C$, the induced endomorphism of $C$ is congruent to the identity modulo $y'.\mathrm{asIdeal}$. (iv) For every $\gamma \in \Gamma_0(M')$ and every level automorphism $\tau$ attached to $\gamma^{-1}$ preserving $C$ and inducing the identity modulo $y'.\mathrm{asIdeal}$, there exist a ring automorphism $\theta$ of $S$, an element $c \in W_1$ and a matrix $M \in \mathrm{M}_2(W_1)$ such that $\theta \circ \varepsilon = \varepsilon \circ \tau|_C$; $\theta$ fixes the classes of all constant series; $\theta(X_{j_0}) \equiv \sum_{i} M_{i j_0} X_i$ modulo the square of the ideal generated by the classes of $X_0, X_1$; $c^{q+1} \equiv 1$ and $M_{i j_0} \equiv c\,\gamma_{i j_0}$ modulo $\mathfrak{m}_{W_1}$; $\gamma_{11} \equiv 1 \pmod \ell$ implies $c \equiv 1$ modulo $\mathfrak{m}_{W_1}$; and if $\gamma \in \Gamma(q)$ and $\tau$ is not the identity then $c \not\equiv 1$ modulo $\mathfrak{m}_{W_1}$. (v) For all integers $a_1,b_1,a_2,b_2$ and all prime ideals $P_1,P_2$ of $S$, each not containing both classes of $X_0$ and $X_1$, each containing the class of $\sigma_1 \varpi$, and each containing an element of the form $a_iX_0 + b_iX_1 + h$ with $h \in (X_0,X_1)^2$, the contractions of $P_1$ and $P_2$ along $e_1 \circ \mathrm{toC}$ differ as soon as $q \nmid a_1b_2 - a_2b_1$. (vi) For a prime $P$ of $S$ with those two first properties and containing an element $1 \cdot X_0 + 0 \cdot X_1 + h$ with $h \in (X_0,X_1)^2$, and for $a \in C$: the image $\mathrm{toC}(\mathrm{germY}(a))$ lies in the contraction of $P$ along $e_1$ if and only if every Laurent coefficient of $a$ lies in the image of $\mathfrak{m}_A$. (vii) There exist a proof that [`ModularCurve.jqNModC L q`](def/ModularCurve_JqCoeff.html#L18) lies in $K$ and in $C$, an element $a_0 \in A$ with that element of $C$ congruent to $a_0$ modulo $y'.\mathrm{asIdeal}$, an integer $e_0 \geq 1$ and a series $h \in (X_0,X_1)^{e_0}$ such that: for all $a,b \in W_1$ not both in $\mathfrak{m}_{W_1}$ with $a^qb - ab^q \in \mathfrak{m}_{W_1}$, the value $\sum_{i=0}^{e_0} (\text{coefficient of } X_0^iX_1^{e_0-i} \text{ in } h)\, a^i b^{e_0-i}$ is a unit; and $\varepsilon$ sends that difference to the class of $h$.
--
--   **The ideal $J$ (`hJ`).** $J$ is the infimum of the set of ideals of $C$ of the form
--   $$(\tau|_C)^{*}\,\varepsilon^{*}\bigl(\sigma_1\varpi_t,\,X_0,\,X_1\bigr)S ,$$
--   the contraction along the restriction of $\tau$ to $C$ of the contraction along $\varepsilon$ of the ideal of $S$ generated by the classes of $\sigma_1\varpi_t$, $X_0$ and $X_1$, as $\gamma$ ranges over $\Gamma(q) \cap \Gamma_0(M')$ and $\tau$ over the level automorphisms attached to $\gamma^{-1}$ preserving $C$.
--
--   **The blow-up algebra (`hB`, `hCB`).** $B$ is the $A$-subalgebra of $K$ obtained by restriction of scalars from the $C$-subalgebra generated by $\{x \in K : x\,\varpi_t \in J\}$, and $C \leq B$.
--
--   **The hypothesis `hK1` (three clauses).** (i) For every $\gamma \in \Gamma_0(M')$, every level automorphism $\tau$ attached to $\gamma^{-1}$ preserving $C$ and inducing the identity modulo $y$, and every $a \in C$: $\varepsilon(a)$ lies in the ideal generated by the classes of $\sigma_1\varpi_t, X_0, X_1$ if and only if $\varepsilon(\tau a)$ does. (ii) For every $\gamma \in \Gamma_0(M')$, every level automorphism $\tau$ attached to $\gamma^{-1}$ and every $a \in C$ with $\tau a \in C$: $a \in J$ if and only if $\tau a \in J$. (iii) Every such $\tau$ maps $B$ into $B$.
--
--   **The hypothesis `hbridge` (eight clauses).** (i) The contraction along $\varepsilon$ of the ideal generated by the classes of $\sigma_1\varpi, X_0, X_1$ equals $y$. (ii) For every $n$ and every $s \in S$ there is $a \in C$ with $\varepsilon(a) - s$ in the $n$-th power of that ideal. (iii) $\varepsilon$ sends $a \in A$ to the class of the constant series $\sigma_1(a)$. (iv) Every element of $C$ is congruent modulo $y$ to an element of $A$. (v) Every element of $W_1$ is congruent modulo $\mathfrak{m}_{W_1}$ to an element of $\sigma_1(A)$. (vi) $\sigma_1^{-1}(\mathfrak{m}_{W_1}) = \mathfrak{m}_A$. (vii) The ideal generated by the classes of $\sigma_1\varpi, X_0, X_1$ is maximal and is the only maximal ideal of $S$. (viii) $S$, viewed as a $C$-algebra through $\varepsilon$, is flat.
--
--   **The hypothesis `hcentre` (four clauses).** (i) The ideal generated by $\varepsilon(J)$ is the ideal of $S$ generated by the classes of $\sigma_1\varpi_t, X_0, X_1$. (ii) There is an ideal $I \subseteq C$ with $J$ equal to the intersection of $I$ with the contraction along $\varepsilon$ of that ideal, and $I + y = C$. (iii) $J \leq y$. (iv) $\varpi_t \in J$.
--
--   Finally, `inst` endows $\kappa_A$ with the structure of an algebra over `GaloisField q 2` $= \mathbb{F}_{q^2}$.
--
--   **Conclusion.** Let $L_{\mathrm{loc}} :=$ `Localization.Away` of $S$ at the class of $\sigma_1\varpi_t$, with structure map $\iota_S : S \to L_{\mathrm{loc}}$, let $x_0, x_1 \in L_{\mathrm{loc}}$ be the products of $\iota_S$ of the classes of $X_0$, respectively $X_1$, with the inverse of the class of $\sigma_1\varpi_t$, and let $R_{\mathrm{loc}} \subseteq L_{\mathrm{loc}}$ be the subring generated by $\iota_S(S) \cup \{x_0,x_1\}$. Write $\mathcal{C} :=$ [`DrinfeldCurve.CoordRing q`](def/DrinfeldCurve_CoordRing.html#L21) $\kappa_A$, the quotient of $\kappa_A[X_0,X_1]$ by the ideal generated by `drinfeldPoly q` $\kappa_A$ $- 1$, with distinguished elements $x$ and $y$ the classes of $X_0$ and $X_1$; let $H :=$ [`DrinfeldCurve.hSubgroup q`](def/DrinfeldCurve_CoordRing.html#L276), the kernel of the character $\mathrm{GL}_2(\mathbb{Z}/q) \times \mathbb{F}_{q^2}^{\times} \to \mathbb{F}_{q^2}^{\times}$, $(g,c) \mapsto \det(g)\,c^{q+1}$, acting on $\mathcal{C}$ by $\kappa_A$-algebra automorphisms through [`DrinfeldCurve.hAction`](def/DrinfeldCurve_CoordRing.html#L325); and let $\bar\gamma :=$ [`ModularCurve.FullLevel.redQ q γ`](def/ModularCurve_FullLevelJacobian.html#L230) be the image of $\gamma$ in $\mathrm{GL}_2(\mathbb{Z}/q)$.
--
--   Then for every ring homomorphism $\Phi : B \to L_{\mathrm{loc}}$, together with the facts that $\iota_S(S) \subseteq R_{\mathrm{loc}}$, $x_0, x_1 \in R_{\mathrm{loc}}$ and $\Phi(B) \subseteq R_{\mathrm{loc}}$, for every ring homomorphism $t_W : W_1 \to \kappa_A$, every $c_R \in \kappa_A$ and all ring homomorphisms $\rho_R : R_{\mathrm{loc}} \to \mathcal{C}$ and $\rho : B \to \mathcal{C}$ satisfying the following fibre-package conditions — $\Phi$ agrees on $C$ with $\iota_S \circ \varepsilon$; for $x \in B$ and $i \in J$ with $x\,\varpi_t = i$ in $K$, $\Phi(x)\,\iota_S(\text{class of } \sigma_1\varpi_t) = \iota_S(\varepsilon(i))$; $t_W \circ \sigma_1$ is the residue map of $A$ and $t_W$ kills $\mathfrak{m}_{W_1}$; $c_R \neq 0$; $\rho_R(\iota_S(\text{class of } F))$ is the image in $\mathcal{C}$ of $t_W(\text{constant coefficient of } F)$ for every $F \in W_1[[X_0,X_1]]$; $\rho_R(x_0) = c_R\,x$ and $\rho_R(x_1) = c_R\,y$; and $\rho = \rho_R \circ \Phi$ — the following two assertions hold.
--
--   First: for every $\gamma \in \Gamma_0(M')$ and every level automorphism $\tau$ attached to $\gamma^{-1}$ which fixes the point $y$ in the sense that for all $b \in C$ with $\tau b \in C$ one has $b \in y \iff \tau b \in y$, there exists $c \in \mathbb{F}_{q^2}^{\times}$ with $(\bar\gamma, c) \in H$ such that: (a) $\rho(\tau b) = h_{(\bar\gamma, c)}(\rho(b))$ for all $b \in B$ with $\tau b \in B$, where $h$ denotes the action of $H$ on $\mathcal{C}$; (b) if $\gamma \in \Gamma(q)$ and $\tau$ is not the identity of $K$, then $c \neq 1$; and (c) the same scalar is realised centrally: there exist $\gamma' \in \Gamma(q) \cap \Gamma_0(M')$ and a level automorphism $\tau'$ attached to $\gamma'^{-1}$ which fixes $y$ in the same sense, with $(1, c) \in H$, such that $\rho(\tau' b) = h_{(1,c)}(\rho(b))$ for all $b \in B$ with $\tau' b \in B$.
--
--   Second: the central involution is realised — there exist $\gamma' \in \Gamma(q) \cap \Gamma_0(M')$ and a level automorphism $\tau'$ attached to $\gamma'^{-1}$ fixing $y$ in the same sense, with $(1,-1) \in H$, such that $\rho(\tau' b) = h_{(1,-1)}(\rho(b))$ for all $b \in B$ with $\tau' b \in B$.
--
--   This is the statement that, at a supersingular point of the integral model of a modular curve of level $\Gamma_{H_1}(q^2M')$, the level automorphisms fixing that point act on the Drinfeld fibre of the blow-up chart through the subgroup $H \subseteq \mathrm{GL}_2(\mathbb{F}_q) \times \mathbb{F}_{q^2}^{\times}$ of pairs $(g,c)$ with $\det(g)c^{q+1} = 1$, with the scalar $c$ non-trivial for non-trivial automorphisms attached to $\Gamma(q)$, and that every scalar so obtained, as well as the central involution, is already realised by an automorphism attached to an element of $\Gamma(q) \cap \Gamma_0(M')$. It is formulated in the auxiliary frame using the $\Gamma_1(\ell)$-diamond condition $\gamma_{11} \equiv 1 \pmod{\ell}$ for a prime $\ell \equiv 11 \pmod{12}$ dividing $M'$, so that it applies for all primes $q$, and it feeds the subsequent analysis of the decomposition and inertia groups at the supersingular fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevelOne_blowupChart_drinfeldFibre_hAction_of_isLevelAutAt_of_fibrePackage_of_dvd.lean

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

theorem ModularCurve.FullLevel.AuxLevelOne.blowupChart_drinfeldFibre_hAction_of_isLevelAutAt_of_fibrePackage_of_dvd
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
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
            ∀ hpres : (∀ a : ↥K, a ∈ chartAlgFin A (↥K) j → τ a ∈ chartAlgFin A (↥K) j),
              (∀ a : ↥(chartAlgFin A (↥K) j),
                (((τ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpres) a : ↥(chartAlgFin A (↥K) j)) - a ∈ y) →
              ∀ a : ↥(chartAlgFin A (↥K) j),
                (e₁ : CMP →+* S) (toC (germY a)) ∈ Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖt)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)} ↔
                (e₁ : CMP →+* S) (toC (germY (((τ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpres) a))) ∈ Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖt)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
            ∀ (a : ↥(chartAlgFin A (↥K) j)) (ha : τ (a : ↥K) ∈ chartAlgFin A (↥K) j),
              a ∈ J ↔ (⟨τ (a : ↥K), ha⟩ : ↥(chartAlgFin A (↥K) j)) ∈ J) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
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
            ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
              (∀ (b : ↥(chartAlgFin A (↥K) j)) (hb : τ (b : ↥K) ∈ chartAlgFin A (↥K) j),
                  b ∈ y ↔ (⟨τ (b : ↥K), hb⟩ : ↥(chartAlgFin A (↥K) j)) ∈ y) →
              ∃ (c : (GaloisField q 2)ˣ) (hmem : (ModularCurve.FullLevel.redQ q γ, c) ∈ DrinfeldCurve.hSubgroup q),
                (∀ (b : ↥B) (hb : τ (b : ↥K) ∈ B), ρ ⟨τ (b : ↥K), hb⟩ = DrinfeldCurve.hAction q (ResidueField A) ⟨_, hmem⟩ (ρ b)) ∧
                (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥K, τ k = k) → c ≠ 1) ∧
                (∃ (γ' : SL(2, ℤ)) (_ : γ' ∈ CongruenceSubgroup.Gamma q) (_ : γ' ∈ CongruenceSubgroup.Gamma0 M') (τ' : ↥K ≃ₐ[L] ↥K)
                   (_ : ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ'⁻¹ K τ')
                   (_ : (∀ (b : ↥(chartAlgFin A (↥K) j)) (hb : τ' (b : ↥K) ∈ chartAlgFin A (↥K) j),
                  b ∈ y ↔ (⟨τ' (b : ↥K), hb⟩ : ↥(chartAlgFin A (↥K) j)) ∈ y))
                   (hmem' : ((1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)), c) ∈ DrinfeldCurve.hSubgroup q),
                   ∀ (b : ↥B) (hb : τ' (b : ↥K) ∈ B), ρ ⟨τ' (b : ↥K), hb⟩ = DrinfeldCurve.hAction q (ResidueField A) ⟨_, hmem'⟩ (ρ b))) ∧

          (∃ (γ' : SL(2, ℤ)) (_ : γ' ∈ CongruenceSubgroup.Gamma q) (_ : γ' ∈ CongruenceSubgroup.Gamma0 M') (τ' : ↥K ≃ₐ[L] ↥K)
             (_ : ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ'⁻¹ K τ')
             (_ : (∀ (b : ↥(chartAlgFin A (↥K) j)) (hb : τ' (b : ↥K) ∈ chartAlgFin A (↥K) j),
                  b ∈ y ↔ (⟨τ' (b : ↥K), hb⟩ : ↥(chartAlgFin A (↥K) j)) ∈ y))
             (hmem' : ((1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)), (-1 : (GaloisField q 2)ˣ)) ∈ DrinfeldCurve.hSubgroup q),
             ∀ (b : ↥B) (hb : τ' (b : ↥K) ∈ B), ρ ⟨τ' (b : ↥K), hb⟩ = DrinfeldCurve.hAction q (ResidueField A) ⟨_, hmem'⟩ (ρ b)) := by sorry
