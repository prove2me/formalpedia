-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_inertia_drinfeldChart_semilinear_linearPart_transport_of_levelAut_linearPart_of_pow_eq_mul_of_isPrimitiveRoot_mul_of_dvd
-- name    : ModularCurve.FullLevel.AuxLevelOne.inertia_drinfeldChart_semilinear_linearPart_transport_of_levelAut_linearPart_of_pow_eq_mul_of_isPrimitiveRoot_mul_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:14.444979+00:00
-- url     : https://prove2.me/theorems/a9150319-ef68-551a-ba51-2d83ee0244a9
-- title:
--   Transport of the semilinear inertia law between two Drinfeld charts
-- statement:
--   **Arithmetic frame.** Fix a prime $q$, a nonzero natural number $M'$ with $q \nmid M'$, and a prime $\ell$ with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$. Let $L$ be a field of characteristic zero, $\zeta \in L$ a primitive $q$-th root of unity and $\xi \in L$ a primitive $(q\ell)$-th root of unity with $\zeta = \xi^{\ell}$, and assume there is a ring homomorphism $\iota : L \to \mathbb{C}$ with $\iota(\xi) = \exp(2\pi i/(q\ell))$. Let $H_1 \le (\mathbb{Z}/q^2M')^{\times}$ be the subgroup $H_1 = \mathrm{levelH}(q,M') \cap \ker\big((\mathbb{Z}/q^2M')^{\times} \to (\mathbb{Z}/\ell)^{\times}\big)$, where [`ModularCurve.FullLevel.levelH`](def/ModularCurve_FullLevelJacobian.html#L22) is the kernel of the reduction $(\mathbb{Z}/q^2M')^{\times} \to (\mathbb{Z}/q)^{\times}$, i.e. the units congruent to $1$ modulo $q$. Let $K$ be the intermediate field $K = \mathrm{laurentBaseChange}\,L\,\big(\mathrm{xHFunctionField}(q^2M')\,H_1\big)$ of $L \subseteq L((T))$, that is, the subfield of $L((T))$ generated over $L$ by the coefficientwise image under [`ModularCurve.coeffEmb`](def/ModularCurve_LaurentCoeff.html#L81) of the $q$-expansion function field of $\Gamma_{H_1}(q^2M')$ over $\mathbb{Q}$.
--
--   **Integral data and the supersingular point.** Let $A$ be a discrete valuation domain with $\mathrm{Frac}(A) = L$ (via the given algebra structure), with algebraically closed residue field, with $q \in \mathfrak{m}_A$ and with $\zeta$ in the image of $A \to L$; let $A$ act on $K$ compatibly with $A \to L \to K$. Let $j \in K$ be nonzero with Laurent expansion $\mathrm{coeffEmb}\,L\,(\mathrm{jq})$, the image of the $q$-expansion of the modular $j$-function, let $\varpi$ generate $\mathfrak{m}_A$, and let $t \in A$ satisfy $t^{q-1} = q\,w$ for some unit $w \in A$. Write $\mathfrak{X} = \mathrm{TwoChartIntegralModel}\,A\,K\,j$, the pushout of the two affine charts $\mathrm{Spec}$ of the integral closures of $A[j]$ and $A[j^{-1}]$ in $K$. Let $z$ be a point of $\mathfrak{X}$ and let $\varpi_z$ be the germ at $z$ of the image of $\varpi$ under the structure morphism $\mathfrak{X} \to \mathrm{Spec}\,A$; it is assumed that $\varpi_z$ lies in the maximal ideal of the stalk $\mathcal{O}_{\mathfrak{X},z}$. Let $y$ be a point of $\mathrm{XFin} = \mathrm{Spec}(\mathrm{chartAlgFin}\,A\,K\,j)$ with `ι Fin`$(y) = z$, and assume the supersingularity hypothesis `hss`: for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi$ from `chartAlgFin` to $\Omega$ with kernel $y$, the element $\varphi(\mathrm{jChartFin})$ lies in $\mathrm{ssJSet}\,q\,\Omega$, i.e. every elliptic Weierstrass curve over $\Omega$ with that $j$-invariant has no nonzero point killed by $q$.
--
--   **The two Drinfeld-chart presentations.** Let $(W_0, \sigma_0, f_0, u_0, v_0, e_0)$ and $(W, \sigma, f, u, v, e)$ be two data of the following shape: $W_0$ (respectively $W$) is a complete discrete valuation domain, $\sigma_0 : A \to W_0$ (respectively $\sigma : A \to W$) is a ring homomorphism with $\mathfrak{m}_{W_0} = (\sigma_0\varpi)$ (respectively $\mathfrak{m}_W = (\sigma\varpi)$), $u_0, v_0$ (respectively $u, v$) are units of the two-variable power series ring, $f_0$ (respectively $f$) agrees with the Drinfeld form $X_0X_1^{q} - X_0^{q}X_1$ modulo $(X_0,X_1)^{q+2}$, and
--   $$e_0 : \widehat{\mathcal{O}}_{\mathfrak{X},z} \;\xrightarrow{\ \sim\ }\; W_0[[X_0,X_1]]/\big(C(\sigma_0 t)v_0 - f_0u_0\big), \qquad e : \widehat{\mathcal{O}}_{\mathfrak{X},z} \;\xrightarrow{\ \sim\ }\; W[[X_0,X_1]]/\big(C(\sigma t)v - fu\big)$$
--   are ring isomorphisms from the $\mathfrak{m}$-adic completion of $\mathcal{O}_{\mathfrak{X},z}$. Write $S_0$ and $S$ for the two quotient rings, $\mathrm{mk}_{S_0}$, $\mathrm{mk}_S$ for the quotient maps, $\mathrm{toC}$ for the map from the stalk to its completion, and $\mathrm{germ}_Y$ for the canonical ring homomorphism from `chartAlgFin` to $\mathcal{O}_{\mathfrak{X},z}$ obtained from the affine identification of the chart `ι Fin` followed by the germ at $z$.
--
--   **Hypothesis groups occurring as antecedents.** Four groups are assumed about the two presentations, together with a geometric-fixing clause.
--
--   *Constants (two clauses, one for each presentation).* For every $a \in A$, the element $e_0$ of the germ at $z$ of the image of $a$ under $\mathfrak{X} \to \mathrm{Spec}\,A$ equals $\mathrm{mk}_{S_0}(C(\sigma_0 a))$; likewise $e$ of that germ equals $\mathrm{mk}_S(C(\sigma a))$.
--
--   *Level-equivariance with linear part (two clauses, one for each presentation, summarised here).* For every $\gamma \in \Gamma_0(M')$, every $L$-algebra automorphism $\tau$ of $K$ satisfying $\mathrm{IsLevelAutAt}\,L\,q\,\zeta\,q\,(q^2M')\,H_1\,\gamma^{-1}\,K\,\tau$, every proof `hpres` that $\tau$ maps `chartAlgFin` into itself, and under the assumption that the induced endomorphism of `chartAlgFin` is congruent to the identity modulo the prime $y$, there exist a ring automorphism $\theta$ of $S_0$, an element $c \in W_0$ and a matrix $M \in \mathrm{Mat}_2(W_0)$ such that $\theta$ intertwines $e_0 \circ \mathrm{toC} \circ \mathrm{germ}_Y$ with the action of $\tau$ on `chartAlgFin`; $\theta$ fixes every constant $\mathrm{mk}_{S_0}(C(w))$, $w \in W_0$; $\theta(\mathrm{mk}_{S_0}(X_{j'})) \equiv \mathrm{mk}_{S_0}\big(\sum_{i} C(M_{ij'})X_i\big)$ modulo the square of the ideal generated by $\mathrm{mk}_{S_0}(X_0), \mathrm{mk}_{S_0}(X_1)$; $c^{q+1} \equiv 1$, $M_{ij'} \equiv c\,\gamma_{ij'}$ modulo $\mathfrak{m}_{W_0}$; $\gamma_{11} \equiv 1 \pmod{\ell}$ implies $c \equiv 1$ modulo $\mathfrak{m}_{W_0}$; and if $\gamma \in \Gamma(q)$ and $\tau$ is not the identity on $K$ then $c - 1 \notin \mathfrak{m}_{W_0}$. The second clause is the same statement with $S_0, W_0, \sigma_0, e_0, \mathrm{mk}_{S_0}$ replaced by $S, W, \sigma, e, \mathrm{mk}_S$. Here $\mathrm{IsLevelAutAt}\,L\,q\,\zeta\,q\,N_0\,H_1\,\delta\,K\,\tau$ asserts: for every weight $k$, all modular forms $f', g'$ of weight $k$ for $\Gamma_{H_1}(N_0)$ with integral $q$-expansions $p_{f'}, p_{g'}$ such that the Laurent series of $p_{g'}$ is nonzero, every $x \in K$ whose Laurent expansion is the image under `coeffEmb` of $p_{f'}/p_{g'}$, and every $\iota : L \to \mathbb{C}$ with $\iota(\zeta) = \exp(2\pi i/q)$, the coefficientwise image of the Laurent series of $\tau x$ under $\iota$, multiplied by the $q$-expansion of $g' \mid_k \mathrm{conjElemN}\,q\,\delta$, equals the $q$-expansion of $f' \mid_k \mathrm{conjElemN}\,q\,\delta$, where $\mathrm{conjElemN}\,q\,\delta = \begin{pmatrix}\delta_{00} & \delta_{01}/q \\ q\,\delta_{10} & \delta_{11}\end{pmatrix}$.
--
--   *Geometric fixing.* For every $\gamma \in \Gamma_0(M')$ with $\gamma_{11} \equiv 1 \pmod{\ell}$, every $\tau$ with $\mathrm{IsLevelAutAt}\,L\,q\,\zeta\,q\,(q^2M')\,H_1\,\gamma^{-1}\,K\,\tau$, every proof that $\tau$ preserves `chartAlgFin`, and every $a$ in `chartAlgFin`, the difference $\tau a - a$ lies in the prime $y$.
--
--   **Conclusion.** Under these hypotheses, the following holds for all $d \in (\mathbb{Z}/q)^{\times}$, all ring automorphisms $\sigma_L$ of $L$ and $\sigma_A$ of $A$ with $\sigma_L$ extending $\sigma_A$ along $A \to L$ and $\sigma_A \equiv \mathrm{id}$ modulo $\mathfrak{m}_A$, all $\pi \in A$ with $\pi^{q^2-1} = q$, all $\alpha \in A$ with $\sigma_A \pi = \alpha\pi$ and $\alpha^{q+1} \equiv d$ (the canonical natural-number representative of $d$) modulo $\mathfrak{m}_A$, and all ring automorphisms $\tau$ of $K$ which act on Laurent expansions coefficientwise by $\sigma_L$, preserve `chartAlgFin` (by a given proof `hpres`) and induce on `chartAlgFin` a map congruent to the identity modulo $y$:
--
--   if there exist a ring automorphism $\theta$ of $S_0$, a ring automorphism $\sigma_W$ of $W_0$, an element $c \in W_0$ and a matrix $M \in \mathrm{Mat}_2(W_0)$ such that
--
--   (i) $\theta$ intertwines $e_0 \circ \mathrm{toC} \circ \mathrm{germ}_Y$ with the action of $\tau$ on `chartAlgFin`;
--   (ii) $\sigma_W \circ \sigma_0 = \sigma_0 \circ \sigma_A$ on $A$;
--   (iii) $\sigma_W w \equiv w$ modulo $\mathfrak{m}_{W_0}$ for all $w \in W_0$;
--   (iv) $\theta(\mathrm{mk}_{S_0}(C(w))) = \mathrm{mk}_{S_0}(C(\sigma_W w))$ for all $w \in W_0$, so $\theta$ is $\sigma_W$-semilinear on constants;
--   (v) $\theta(\mathrm{mk}_{S_0}(X_{j'})) - \mathrm{mk}_{S_0}\big(\sum_i C(M_{ij'})X_i\big)$ lies in the square of the ideal generated by $\mathrm{mk}_{S_0}(X_0)$ and $\mathrm{mk}_{S_0}(X_1)$, for each $j' \in \{0,1\}$;
--   (vi) $c \equiv \sigma_0(\alpha^{q+1})$ modulo $\mathfrak{m}_{W_0}$;
--   (vii) $M_{ij'} \equiv c \cdot \big(\mathrm{diagOneElem}\,q\,(d^{q})^{-1}\big)_{ij'}$ modulo $\mathfrak{m}_{W_0}$ for all $i,j'$, where $\mathrm{diagOneElem}\,q\,\varepsilon$ is the matrix $\begin{pmatrix}1 & 0\\ 0 & \varepsilon\end{pmatrix}$ in $\mathrm{GL}_2(\mathbb{Z}/q)$ and its entries are lifted to $W_0$ through their canonical natural-number representatives;
--
--   then there exist a ring automorphism $\theta$ of $S$, a ring automorphism $\sigma_W$ of $W$, an element $c \in W$ and a matrix $M \in \mathrm{Mat}_2(W)$ satisfying the same seven conditions with $S_0, W_0, \sigma_0, e_0, \mathrm{mk}_{S_0}$ replaced by $S, W, \sigma, e, \mathrm{mk}_S$: $\theta$ intertwines $e \circ \mathrm{toC} \circ \mathrm{germ}_Y$ with $\tau$, $\sigma_W \circ \sigma = \sigma \circ \sigma_A$, $\sigma_W$ is trivial modulo $\mathfrak{m}_W$, $\theta$ is $\sigma_W$-semilinear on constants, $\theta$ has linear part $M$ modulo the square of the ideal generated by the images of $X_0, X_1$, $c \equiv \sigma(\alpha^{q+1})$ modulo $\mathfrak{m}_W$, and $M_{ij'} \equiv c \cdot \big(\mathrm{diagOneElem}\,q\,(d^{q})^{-1}\big)_{ij'}$ modulo $\mathfrak{m}_W$.
--
--   This is a comparison step in the local analysis at a supersingular point of the integral model of the modular curve of level $H_1 \le (\mathbb{Z}/q^2M')^{\times}$: the semilinear action of an inertia element, with its prescribed linear part governed by the diagonal matrix $\mathrm{diag}(1,(d^{q})^{-1})$ and the constant $\sigma(\alpha^{q+1})$, is transferred from one Drinfeld-chart presentation of the completed local ring to any other. It is used by the tame-character statement [`ModularCurve.FullLevel.AuxLevelOne.inertia_drinfeldChart_semilinear_linearPart_tameCharacter_diagOneElem_of_levelAut_linearPart_of_pow_eq_mul_of_isPrimitiveRoot_mul_of_dvd`](thm.html#ModularCurve.FullLevel.AuxLevelOne.inertia_drinfeldChart_semilinear_linearPart_tameCharacter_diagOneElem_of_levelAut_linearPart_of_pow_eq_mul_of_isPrimitiveRoot_mul_of_dvd), the $q$-generic ($q \in \{2,3\}$) variant of the corresponding statement at higher level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevelOne_inertia_drinfeldChart_semilinear_linearPart_transport_of_levelAut_linearPart_of_pow_eq_mul_of_isPrimitiveRoot_mul_of_dvd.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

open scoped MatrixGroups

theorem ModularCurve.FullLevel.AuxLevelOne.inertia_drinfeldChart_semilinear_linearPart_transport_of_levelAut_linearPart_of_pow_eq_mul_of_isPrimitiveRoot_mul_of_dvd
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')

    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (hζξ : ζ = ξ ^ ℓ)
    (hι : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [IsAlgClosed (IsLocalRing.ResidueField A)]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})

    (t : A) (ht : ∃ w : A, IsUnit w ∧ t ^ (q - 1) = (q : A) * w)
    (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j))
    (ϖz : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
    (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
      (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
    (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
    (y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j))
    (hy : (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y = z)
    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω),
      RingHom.ker φ = y.asIdeal →
        φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω)

    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (IsLocalRing.maximalIdeal W₀) W₀] (σ₀ : A →+* W₀)
    (hσϖ₀ : IsLocalRing.maximalIdeal W₀ = Ideal.span {σ₀ ϖ})
    (f₀ u₀ v₀ : MvPowerSeries (Fin 2) W₀) (hu₀ : IsUnit u₀) (hv₀ : IsUnit v₀)
    (hf₀ : f₀ - DrinfeldCurve.LocalChart.drinfeldForm q W₀ ∈
      (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₀), MvPowerSeries.X 1}) ^ (q + 2))
    (e₀ : AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ≃+*
      MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {MvPowerSeries.C (σ₀ t) * v₀ - f₀ * u₀})

    (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W] (σ : A →+* W)
    (hσϖ : IsLocalRing.maximalIdeal W = Ideal.span {σ ϖ})
    (f u v : MvPowerSeries (Fin 2) W) (hu : IsUnit u) (hv : IsUnit v)
    (hf : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
      (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (q + 2))
    (e : AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ≃+*
      MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ t) * v - f * u}) :

      let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
      let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
      let toC : STK →+* CMP := algebraMap STK CMP
      let S := (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ t) * v - f * u})
      let mkS : MvPowerSeries (Fin 2) W →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ t) * v - f * u})
      let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
        ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
            ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y, trivial, hy⟩).hom.comp
          ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
            (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)
      let S₀ := (MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {MvPowerSeries.C (σ₀ t) * v₀ - f₀ * u₀})
      let mkS₀ : MvPowerSeries (Fin 2) W₀ →+* S₀ := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ₀ t) * v₀ - f₀ * u₀})

      (∀ a : A, e₀ (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
            (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
          (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
            (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
              ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)))) =
        Ideal.Quotient.mk _ (MvPowerSeries.C (σ₀ a))) →

      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
        ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
          ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
              τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
            (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
              (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
              (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y.asIdeal) →
              ∃ (θ : S₀ ≃+* S₀) (c : W₀) (M : Matrix (Fin 2) (Fin 2) W₀),

                (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                  θ (e₀ (toC (germY a))) = e₀ (toC (germY (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
              (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a)))) ∧

                (∀ w : W₀, θ (mkS₀ (MvPowerSeries.C w)) = mkS₀ (MvPowerSeries.C w)) ∧

                (∀ jj : Fin 2, θ (mkS₀ (MvPowerSeries.X jj)) -
                    mkS₀ (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) ∈
                  (Ideal.span {mkS₀ (MvPowerSeries.X 0), mkS₀ (MvPowerSeries.X 1)}) ^ 2) ∧
                (c ^ (q + 1) - 1 ∈ IsLocalRing.maximalIdeal W₀) ∧
                (∀ ii jj : Fin 2, M ii jj - c * ((γ ii jj : ℤ) : W₀) ∈ IsLocalRing.maximalIdeal W₀) ∧
                (((γ 1 1 : ℤ) : ZMod ℓ) = 1 → c - 1 ∈ IsLocalRing.maximalIdeal W₀) ∧

                (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥K, τ k = k) → c - 1 ∉ IsLocalRing.maximalIdeal W₀)) →

      (∀ a : A, e (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
            (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
          (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
            (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
              ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)))) =
        Ideal.Quotient.mk _ (MvPowerSeries.C (σ a))) →

      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
        ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
          ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
              τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
            (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
              (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
              (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y.asIdeal) →
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

                (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥K, τ k = k) → c - 1 ∉ IsLocalRing.maximalIdeal W)) →

      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' → ((γ 1 1 : ℤ) : ZMod ℓ) = 1 →
        ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
          ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
              τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
            ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
              (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
              (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y.asIdeal) →

    ∀ (d : (ZMod q)ˣ) (σL : L ≃+* L) (σA : A ≃+* A),
      (∀ a : A, algebraMap A L (σA a) = σL (algebraMap A L a)) →

      (∀ a : A, σA a - a ∈ IsLocalRing.maximalIdeal A) →

      ∀ (π : A), π ^ (q ^ 2 - 1) = (q : A) → ∀ (αt : A), σA π = αt * π →
      αt ^ (q + 1) - (((d : ZMod q).val : ℕ) : A) ∈ IsLocalRing.maximalIdeal A →
      ∀ τ : ↥K ≃+* ↥K,

        (∀ x : ↥K, ((τ x : ↥K) : LaurentSeries L) = ModularCurve.coeffMap σL.toRingHom ((x : ↥K) : LaurentSeries L)) →
        ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
            τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),

          (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
            (((τ.toRingHom.restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
              (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y.asIdeal)) →

          (∃ (θ : S₀ ≃+* S₀) (σW : W₀ ≃+* W₀) (ct : W₀) (M : Matrix (Fin 2) (Fin 2) W₀),
            (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
              θ (e₀ (toC (germY a))) = e₀ (toC (germY ((τ.toRingHom.restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
              (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a)))) ∧
            (∀ a : A, σW (σ₀ a) = σ₀ (σA a)) ∧
            (∀ w : W₀, σW w - w ∈ IsLocalRing.maximalIdeal W₀) ∧
            (∀ w : W₀, θ (mkS₀ (MvPowerSeries.C w)) = mkS₀ (MvPowerSeries.C (σW w))) ∧
            (∀ jj : Fin 2, θ (mkS₀ (MvPowerSeries.X jj)) -
                mkS₀ (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) ∈
              (Ideal.span {mkS₀ (MvPowerSeries.X 0), mkS₀ (MvPowerSeries.X 1)}) ^ 2) ∧

            (ct - σ₀ (αt ^ (q + 1)) ∈ IsLocalRing.maximalIdeal W₀) ∧
            (∀ ii jj : Fin 2, M ii jj -
                ct * (((((ModularCurve.FullLevel.diagOneElem q (d ^ q)⁻¹ : CuspidalType.GL2 q) :
                    Matrix (Fin 2) (Fin 2) (ZMod q)) ii jj).val : ℕ) : W₀) ∈ IsLocalRing.maximalIdeal W₀)) →

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
                    Matrix (Fin 2) (Fin 2) (ZMod q)) ii jj).val : ℕ) : W) ∈ IsLocalRing.maximalIdeal W) := by sorry
