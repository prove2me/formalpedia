-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevel_inertia_drinfeldChart_semilinear_linearPart_transport_of_levelAut_linearPart_of_pow_eq_mul_of_isAlgClosed
-- name    : ModularCurve.FullLevel.AuxLevel.inertia_drinfeldChart_semilinear_linearPart_transport_of_levelAut_linearPart_of_pow_eq_mul_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:22.181174+00:00
-- url     : https://prove2.me/theorems/99cc3ed7-62bd-5391-bdb2-fc00b2e8d8b2
-- title:
--   Transport of the semilinear tame-inertia law between Drinfeld charts
-- statement:
--   Fix a prime $q \ge 5$, a non-zero natural number $M'$ with $q \nmid M'$, and a prime $\ell \ge 3$ with $\ell \ne q$ and $\ell \nmid M'$. Let $L$ be a field of characteristic zero carrying a primitive $q$-th root of unity $\zeta$ and a primitive $(q\ell)$-th root of unity $\xi$, and assume (`hι`) that there is a ring homomorphism $\iota : L \to \mathbb{C}$ with $\iota\xi = \exp(2\pi i/(q\ell))$. Let $K$ be an intermediate field of $L \subseteq \mathrm{LaurentSeries}\,L$ which, by `hK`, is [`ModularCurve.laurentBaseChange`](def/ModularCurve_LaurentCoeff.html#L103) of the $q$-expansion function field [`ModularCurve.xHFunctionField`](def/ModularCurve_XH.html#L79) of level $(q\ell)^2M'$ for the subgroup [`ModularCurve.FullLevel.levelH`](def/ModularCurve_FullLevelJacobian.html#L22) $(q\ell)\,M'$, the kernel of the reduction $(\mathbb{Z}/(q\ell)^2M')^{\times} \to (\mathbb{Z}/(q\ell))^{\times}$; thus $K$ is generated over $L$ by the coefficientwise images of that rational function field.
--
--   Let $A$ be a discrete valuation domain with $L$ as fraction field and with algebraically closed residue field, such that $q$ lies in the maximal ideal of $A$ (`hAq`) and $\zeta$ lies in the image of $A$ (`hζA`), together with an $A$-algebra structure on $K$ compatible with that on $L$. Let $j \in K$ be the element whose Laurent expansion is [`ModularCurve.coeffEmb`](def/ModularCurve_LaurentCoeff.html#L81) of [`ModularCurve.jq`](def/ModularCurve_X0.html#L157), assumed non-zero, let $\varpi$ generate the maximal ideal of $A$, and let $t \in A$ satisfy $t^{q-1} = q\,w$ for some unit $w$ (`ht`).
--
--   On the two-chart integral model $\mathfrak{X} =$ [`AlgebraicCurve.TwoChartIntegralModel`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) $A\,K\,j$ (the pushout of the two affine charts $\operatorname{Spec}$ of the integral closures of $A[j]$ and $A[j^{-1}]$ in $K$) let $z$ be a point, let $\varpi_z$ be the germ at $z$ of the image of $\varpi$ under the structure morphism `toBase` to $\operatorname{Spec} A$ (`hϖz`), assumed to lie in the maximal ideal of the stalk (`hz`), and let $y$ be a point of `XFin` $=\operatorname{Spec}$ of the chart algebra `chartAlgFin` $A\,K\,j$ with `ιFin` $y = z$ (`hy`). The supersingularity hypothesis `hss` requires that for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi$ from the chart algebra to $\Omega$ with kernel $y$, the value $\varphi(\mathtt{jChartFin})$ lies in [`ModularCurve.ssJSet`](def/ModularCurve_SupersingularModuli.html#L7) $q\,\Omega$, i.e. every elliptic curve over $\Omega$ with that $j$-invariant has no non-trivial $q$-torsion point.
--
--   Two Drinfeld-chart data at $z$ are given. The first (CHART$_0$) consists of a complete discrete valuation domain $W_0$, a ring homomorphism $\sigma_0 : A \to W_0$ carrying $\varpi$ to a generator of the maximal ideal of $W_0$ (`hσϖ₀`), power series $f_0, u_0, v_0 \in W_0[[X_0,X_1]]$ with $u_0, v_0$ units and $f_0 \equiv \mathtt{drinfeldForm}\,q\,W_0 = X_0X_1^q - X_0^qX_1 \pmod{(X_0,X_1)^{q+2}}$ (`hf₀`), and a ring isomorphism $e_0$ from the adic completion of the stalk of $\mathfrak{X}$ at $z$ with respect to its maximal ideal onto $S_0 = W_0[[X_0,X_1]]/(C(\sigma_0 t)v_0 - f_0u_0)$. The second (CHART) consists of the analogous data $W, \sigma, f, u, v, e$ with quotient $S = W[[X_0,X_1]]/(C(\sigma t)v - fu)$. Abbreviations are introduced for the stalk, its completion `CMP`, the canonical map `toC` from the stalk to the completion, the quotient maps $\mathtt{mkS}$ and $\mathtt{mkS₀}$, and for the canonical homomorphism `germY` from the chart algebra `chartAlgFin` $A\,K\,j$ to the stalk at $z$ obtained from the affine identification of `XFin` and the germ along the open image of `ιFin`.
--
--   Four hypotheses are imposed on these data, each a hypothesis of the implication.
--
--   (CONST$_0$) For every $a \in A$, the isomorphism $e_0$ sends the image in the completion of the germ at $z$ of $a$ (pulled back through `toBase`) to the class of the constant series $C(\sigma_0 a)$.
--
--   (EQ$_0$) For every $\gamma \in \Gamma_0(M')$ and every $L$-algebra automorphism $\tau$ of $K$ satisfying [`ModularCurve.FullLevel.IsLevelAutAt`](def/ModularCurve_FullLevelLevelAutAt.html#L29) $L\,(q\ell)\,\xi\,(q\ell)\,((q\ell)^2M')\,(\mathtt{levelH}\,(q\ell)\,M')\,\gamma^{-1}\,K\,\tau$ — that is, $\tau$ acts on ratios of integral $q$-expansions of modular forms of level $\Gamma_H$ by the slash action of the matrix `conjElemN` $(q\ell)\,\gamma^{-1}$, read through any embedding $\iota$ with $\iota\xi = \exp(2\pi i/(q\ell))$ — and for every witness that $\tau$ preserves the chart algebra, if the induced endomorphism of the chart algebra is congruent to the identity modulo the prime $y$, then there exist a ring automorphism $\theta$ of $S_0$, an element $c \in W_0$ and a matrix $M \in M_2(W_0)$ such that: $\theta$ intertwines $e_0 \circ \mathtt{toC} \circ \mathtt{germY}$ with the action of $\tau$ on the chart algebra; $\theta$ fixes every constant $C(w)$, $w \in W_0$; for each $j$, $\theta(X_j) - \sum_i C(M_{ij})X_i$ lies in the square of the ideal generated by the classes of $X_0, X_1$; $c^{q+1} \equiv 1$ modulo the maximal ideal of $W_0$; $M_{ij} \equiv c\,\gamma_{ij}$ modulo the maximal ideal for all $i,j$; if $\gamma \in \Gamma(\ell)$ then $c \equiv 1$; and if $\gamma \in \Gamma(q)$ and $\tau$ is not the identity on $K$ then $c \not\equiv 1$.
--
--   (CONST) and (EQ) The two preceding conditions verbatim for the second datum, with $\sigma_0, e_0, S_0, \mathtt{mkS₀}, W_0$ replaced by $\sigma, e, S, \mathtt{mkS}, W$.
--
--   (FIX) For every $\gamma$ lying in both $\Gamma_0(M')$ and $\Gamma(\ell)$, every $\tau$ with the above level property for $\gamma^{-1}$ and every witness that $\tau$ preserves the chart algebra, the induced endomorphism of the chart algebra is congruent to the identity modulo the prime $y$.
--
--   Under these hypotheses the following holds. Let $d \in (\mathbb{Z}/q)^{\times}$, let $\sigma_L$ be a ring automorphism of $L$ and $\sigma_A$ a ring automorphism of $A$ compatible with it along $A \to L$, with $\sigma_A a \equiv a$ modulo the maximal ideal of $A$ for all $a$. Let $\pi \in A$ satisfy $\pi^{q^2-1} = q$, let $\tilde\alpha \in A$ satisfy $\sigma_A\pi = \tilde\alpha\pi$, and assume $\tilde\alpha^{q+1} \equiv (d.\mathrm{val} : A)$ modulo the maximal ideal of $A$. Let $\tau$ be a ring automorphism of $K$ acting coefficientwise through $\sigma_L$ on Laurent expansions, preserving the chart algebra, and inducing on the chart algebra an endomorphism congruent to the identity modulo the prime $y$.
--
--   Then: if there exist a ring automorphism $\theta$ of $S_0$, a ring automorphism $\sigma_W$ of $W_0$, an element $\tilde c \in W_0$ and a matrix $M \in M_2(W_0)$ such that (i) $\theta$ intertwines $e_0 \circ \mathtt{toC} \circ \mathtt{germY}$ with the action of $\tau$ on the chart algebra, (ii) $\sigma_W \circ \sigma_0 = \sigma_0 \circ \sigma_A$ on $A$, (iii) $\sigma_W w \equiv w$ modulo the maximal ideal of $W_0$ for all $w$, (iv) $\theta(C(w)) = C(\sigma_W w)$ for all $w \in W_0$, (v) for each $j$, $\theta(X_j) - \sum_i C(M_{ij})X_i$ lies in the square of the ideal generated by the classes of $X_0, X_1$, (vi) $\tilde c \equiv \sigma_0(\tilde\alpha^{q+1})$ modulo the maximal ideal of $W_0$, and (vii) $M_{ij} \equiv \tilde c\,(\mathtt{diagOneElem}\,q\,(d^q)^{-1})_{ij}$ modulo the maximal ideal of $W_0$ for all $i,j$, where [`ModularCurve.FullLevel.diagOneElem`](def/ModularCurve_FullLevelJacobian.html#L233) $q\,e$ is the matrix $\mathrm{diag}(1,e)$ over $\mathbb{Z}/q$ and its entries are lifted by the canonical representative in $\{0,\dots,q-1\}$ — then there exist a ring automorphism $\theta$ of $S$, a ring automorphism $\sigma_W$ of $W$, an element $\tilde c \in W$ and a matrix $M \in M_2(W)$ satisfying the seven conditions (i)–(vii) with $S_0, W_0, e_0, \sigma_0, \mathtt{mkS₀}$ replaced by $S, W, e, \sigma, \mathtt{mkS}$.
--
--   This is the comparison step which carries the semilinear description of the action of an inertial automorphism on a Drinfeld local chart at a supersingular point of the integral model of the modular curve of level $\Gamma(q\ell) \cap \Gamma_0(M')$ from one chart presentation to another, so that the tame-character normalisation $\tilde c \equiv \sigma(\tilde\alpha^{q+1})$ with reduced linear part $\tilde c\,\mathrm{diag}(1,(d^q)^{-1})$ is independent of the chosen Drinfeld datum. It is used by the companion result producing the tame-inertia law with linear part `diagOneElem` for an arbitrary such datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevel_inertia_drinfeldChart_semilinear_linearPart_transport_of_levelAut_linearPart_of_pow_eq_mul_of_isAlgClosed.lean

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

theorem ModularCurve.FullLevel.AuxLevel.inertia_drinfeldChart_semilinear_linearPart_transport_of_levelAut_linearPart_of_pow_eq_mul_of_isAlgClosed
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (hι : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
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
        ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
            (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
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
                (γ ∈ CongruenceSubgroup.Gamma ℓ → c - 1 ∈ IsLocalRing.maximalIdeal W₀) ∧

                (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥K, τ k = k) → c - 1 ∉ IsLocalRing.maximalIdeal W₀)) →

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
                (γ ∈ CongruenceSubgroup.Gamma ℓ → c - 1 ∈ IsLocalRing.maximalIdeal W) ∧

                (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥K, τ k = k) → c - 1 ∉ IsLocalRing.maximalIdeal W)) →

      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' → γ ∈ CongruenceSubgroup.Gamma ℓ →
        ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
            (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
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
